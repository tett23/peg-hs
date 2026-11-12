import { appendFileSync, readFileSync } from 'node:fs';
import { cases } from './lsp-latency.mjs';

const limitSeconds = 0.016;

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

if (import.meta.main) {
  const rows = summarize(process.argv.slice(2).map(file => JSON.parse(readFileSync(file, 'utf8'))));
  const exceeded = rows.filter(row => row.seconds > limitSeconds);
  console.log('| Grammar | Edit | Median (ms) | > 16 ms |');
  console.log('| --- | --- | ---: | --- |');
  for (const { grammar, name, seconds } of rows) {
    console.log(`| ${grammar} | ${name} | ${seconds * 1000} | ${seconds > limitSeconds ? 'yes' : 'no'} |`);
  }
  if (process.env.GITHUB_OUTPUT) {
    appendFileSync(process.env.GITHUB_OUTPUT, `exceeded=${JSON.stringify(exceeded)}\n`);
  }
}
