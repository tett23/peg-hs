import { appendFileSync, readFileSync } from 'node:fs';

// The twelve cases are these six for each of Memo and Golem. An operation
// is the diagnostics of an edit, or the semantic tokens after it (ADR 0102).
const operations = {
  diagnostics: 'range: decode, check, encode',
  'semantic-tokens': 'range, and the semantic tokens',
};

export const cases = ['start', 'middle', 'end'].flatMap(place =>
  Object.values(operations).map(operation => `an edit at the ${place}, ${operation}`));

// The budget of each median (ADR 0071, ADR 0102); docs/budgets.md has it in
// ms.
export const limitSeconds = 0.016;

function median(report) {
  const { reportName, reportKeys, reportMeasured } = report;
  if (!Array.isArray(reportKeys) || !Array.isArray(reportMeasured) || reportMeasured.length === 0) {
    throw new Error(`Missing samples or columns: ${reportName}`);
  }
  const column = key => {
    if (reportKeys.filter(value => value === key).length !== 1) {
      throw new Error(`Missing or duplicate ${key} column: ${reportName}`);
    }
    return reportKeys.indexOf(key);
  };
  const timeIndex = column('time');
  const itersIndex = column('iters');
  const samples = reportMeasured.map(sample => {
    if (!Array.isArray(sample) || sample.length !== reportKeys.length) {
      throw new Error(`Invalid sample columns: ${reportName}`);
    }
    const time = sample[timeIndex];
    const iters = sample[itersIndex];
    if (typeof time !== 'number' || !Number.isFinite(time) || time <= 0 ||
        !Number.isSafeInteger(iters) || iters <= 0) {
      throw new Error(`Invalid sample time or iterations: ${reportName}`);
    }
    const seconds = time / iters;
    if (!Number.isFinite(seconds) || seconds <= 0) {
      throw new Error(`Invalid time per iteration: ${reportName}`);
    }
    return seconds;
  }).sort((left, right) => left - right);
  const middle = Math.floor(samples.length / 2);
  return samples.length % 2 === 1
    ? samples[middle]
    : samples[middle - 1] + (samples[middle] - samples[middle - 1]) / 2;
}

function measurements(input) {
  if (!Array.isArray(input) || input.length !== 3 || input[0] !== 'criterion' ||
      typeof input[1] !== 'string' || !input[1].startsWith('1.6.') ||
      !Array.isArray(input[2])) {
    throw new Error('Expected a Criterion 1.6 report');
  }
  const values = new Map();
  for (const report of input[2]) {
    const match = /^lsp \(\d+ lines\)\/(.*)$/.exec(report?.reportName);
    if (!match || !cases.includes(match[1])) continue;
    const name = match[1];
    if (values.has(name)) throw new Error(`Duplicate measurement: ${name}`);
    values.set(name, median(report));
  }
  for (const name of cases) {
    if (!values.has(name)) throw new Error(`Missing measurement: ${name}`);
  }
  return values;
}

export function summarize(inputs) {
  if (!Array.isArray(inputs) || inputs.length !== 2) {
    throw new Error('Expected Memo and Golem reports');
  }
  return inputs.flatMap((input, index) => {
    const grammar = ['Memo', 'Golem'][index];
    const values = measurements(input);
    return cases.map(name => ({ grammar, name, seconds: values.get(name) }));
  });
}

// Whether every median is within the budget, compared before rounding.
export function passes(rows) {
  return rows.every(row => row.seconds <= limitSeconds);
}

// The largest median of the six cases of an operation, in ms with three
// decimals.
export function largest(rows, operation) {
  const suffix = operations[operation];
  if (!Object.hasOwn(operations, operation)) {
    throw new Error(`Expected diagnostics or semantic-tokens: ${operation}`);
  }
  const values = rows.filter(row => row.name.endsWith(suffix)).map(row => row.seconds);
  if (values.length !== 6) throw new Error(`Expected six cases of ${operation}`);
  return (Math.max(...values) * 1000).toFixed(3);
}

function table(rows) {
  console.log('| Grammar | Edit | Median (ms) | > 16 ms |');
  console.log('| --- | --- | ---: | --- |');
  for (const { grammar, name, seconds } of rows) {
    console.log(`| ${grammar} | ${name} | ${seconds * 1000} | ${seconds > limitSeconds ? 'yes' : 'no'} |`);
  }
}

const read = files => {
  if (files.length !== 2) throw new Error('Pass the Memo and Golem reports');
  return summarize(files.map(file => JSON.parse(readFileSync(file, 'utf8'))));
};

// node scripts/lsp-median.mjs MEMO GOLEM
//   prints the twelve medians, and writes the cases over the budget to
//   GITHUB_OUTPUT for the issue of main (ADR 0099).
// node scripts/lsp-median.mjs --fail-on-exceed MEMO GOLEM
//   prints the twelve medians, and fails when one is over the budget; a pull
//   request passes these reports of its head only (ADR 0102).
// node scripts/lsp-median.mjs --max OPERATION MEMO GOLEM
//   prints the largest median of the operation in ms (ADR 0102).
if (import.meta.main) {
  const args = process.argv.slice(2);
  if (args[0] === '--max') {
    const rows = read(args.slice(2));
    console.log(largest(rows, args[1]));
  } else if (args[0] === '--fail-on-exceed') {
    const rows = read(args.slice(1));
    table(rows);
    if (!passes(rows)) process.exitCode = 1;
  } else {
    const rows = read(args);
    const exceeded = rows.filter(row => row.seconds > limitSeconds);
    table(rows);
    if (process.env.GITHUB_OUTPUT) {
      appendFileSync(process.env.GITHUB_OUTPUT, `exceeded=${JSON.stringify(exceeded)}\n`);
    }
  }
}
