import { readFileSync } from 'node:fs';

const cases = ['start', 'middle', 'end'].flatMap(place =>
  ['range: decode, check, encode', 'range, and the semantic tokens']
    .map(operation => `an edit at the ${place}, ${operation}`));

function means([format, version, reports]) {
  if (format !== 'criterion' || !version.startsWith('1.6.')) {
    throw new Error('Expected a Criterion 1.6 report');
  }
  const values = new Map();
  for (const { reportName, reportAnalysis } of reports) {
    const name = reportName.replace(/^lsp \(\d+ lines\)\//, '');
    if (!cases.includes(name) || name === reportName) continue;
    const seconds = reportAnalysis.anMean.estPoint;
    if (!Number.isFinite(seconds) || seconds <= 0 || values.has(name)) {
      throw new Error(`Invalid or duplicate measurement: ${reportName}`);
    }
    values.set(name, seconds);
  }
  for (const name of cases) {
    if (!values.has(name)) throw new Error(`Missing measurement: ${name}`);
  }
  return values;
}

export function compare(inputs) {
  if (inputs.length !== 4) throw new Error('Expected base and head reports for both grammars');
  const [baseMemo, baseGolem, headMemo, headGolem] = inputs.map(means);
  return [['Memo', baseMemo, headMemo], ['Golem', baseGolem, headGolem]]
    .flatMap(([grammar, base, head]) =>
      cases.map(name => ({ grammar, name, base: base.get(name), head: head.get(name) })));
}

export function passes(rows) {
  return rows.every(row => row.head <= 0.016);
}

if (import.meta.main) {
  const rows = compare(process.argv.slice(2).map(file => JSON.parse(readFileSync(file, 'utf8'))));
  console.log('| Grammar | Edit | Base (ms) | Head (ms) | ≤ 16 ms |');
  console.log('| --- | --- | ---: | ---: | --- |');
  for (const { grammar, name, base, head } of rows) {
    console.log(`| ${grammar} | ${name} | ${base * 1000} | ${head * 1000} | ${head <= 0.016 ? 'pass' : 'fail'} |`);
  }
  if (!passes(rows)) process.exitCode = 1;
}
