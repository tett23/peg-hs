import assert from 'node:assert/strict';
import test from 'node:test';
import { compare, passes } from './lsp-latency.mjs';

function reports() {
  return Array.from({ length: 4 }, () => ['criterion', '1.6.5.0',
    ['start', 'middle', 'end'].flatMap(place =>
      ['range: decode, check, encode', 'range, and the semantic tokens'].map(operation => ({
        reportName: `lsp (712 lines)/an edit at the ${place}, ${operation}`,
        reportAnalysis: { anMean: { estPoint: 0.016 } }
      })))]);
}

test('invariant 1: the inclusive threshold applies only to the head', () => {
  const inputs = reports();
  inputs[0][2][0].reportAnalysis.anMean.estPoint = 0.1;
  assert.equal(compare(inputs).length, 12);
  assert.equal(passes(compare(inputs)), true);
  inputs[2][2][0].reportAnalysis.anMean.estPoint = 0.016001;
  assert.equal(passes(compare(inputs)), false);
});

test('invariant 1: incomplete, duplicate and invalid measurements fail', () => {
  for (const mutate of [
    rows => rows.pop(),
    rows => rows.push(rows[0]),
    ...[0, -1, NaN, Infinity, null].map(value =>
      rows => { rows[0].reportAnalysis.anMean.estPoint = value; })
  ]) {
    for (const index of [0, 1, 2, 3]) {
      const inputs = reports();
      mutate(inputs[index][2]);
      assert.throws(() => compare(inputs));
    }
  }
});
