import assert from 'node:assert/strict';
import test from 'node:test';
import { notify } from './lsp-median-issue.mjs';

const baseEnv = {
  GITHUB_TOKEN: 'test-token',
  GITHUB_REPOSITORY: 'example/peg-hs',
  GITHUB_RUN_ID: '42',
  GITHUB_SERVER_URL: 'https://github.com',
  GITHUB_SHA: 'a'.repeat(40),
};
const exceeded = [{ grammar: 'Golem', name: 'middle, range, and the semantic tokens', seconds: 0.016001 }];

function response(value, status = 200) {
  return { ok: status >= 200 && status < 300, status, json: async () => value };
}

function mockApi({ issues = [], comments = {} } = {}) {
  const calls = [];
  const fetchImpl = async (url, options = {}) => {
    const method = options.method ?? 'GET';
    calls.push({ url: String(url), method, body: options.body && JSON.parse(options.body) });
    const parsed = new URL(url);
    const page = Number(parsed.searchParams.get('page') ?? '1');
    if (method === 'GET' && parsed.pathname.endsWith('/issues')) {
      return response(issues.slice((page - 1) * 100, page * 100));
    }
    const match = parsed.pathname.match(/\/issues\/(\d+)\/comments$/);
    if (method === 'GET' && match) {
      const rows = comments[match[1]] ?? [];
      return response(rows.slice((page - 1) * 100, page * 100));
    }
    if (method === 'POST' && parsed.pathname.endsWith('/issues')) {
      const created = { number: issues.length + 1, state: 'open', body: JSON.parse(options.body).body, user: { login: 'github-actions[bot]' } };
      issues.push(created);
      return response(created, 201);
    }
    if (method === 'POST' && match) {
      (comments[match[1]] ??= []).push({ body: JSON.parse(options.body).body, user: { login: 'github-actions[bot]' } });
      return response({}, 201);
    }
    throw new Error(`unexpected ${method} ${url}`);
  };
  return { calls, fetchImpl };
}

function env(rows = exceeded) {
  return { ...baseEnv, EXCEEDED: JSON.stringify(rows) };
}

test('invariant 2: no exceedance makes no API call', async () => {
  const api = mockApi();
  await notify({ env: env([]), fetchImpl: api.fetchImpl });
  assert.equal(api.calls.length, 0);
});

test('invariant 3: creates one issue containing every exceeded case', async () => {
  const api = mockApi();
  const rows = [...exceeded, { grammar: 'Memo', name: 'start, range: decode, check, encode', seconds: 0.018 }];
  await notify({ env: env(rows), fetchImpl: api.fetchImpl });
  const posts = api.calls.filter(call => call.method === 'POST');
  assert.equal(posts.length, 1);
  assert.match(posts[0].body.body, /Golem/);
  assert.match(posts[0].body.body, /Memo/);
  assert.match(posts[0].body.body, /actions\/runs\/42/);
});

test('invariant 3: appends to an open issue and ignores the same run on retry', async () => {
  const api = mockApi();
  await notify({ env: env(), fetchImpl: api.fetchImpl });
  const newEnv = { ...env(), GITHUB_RUN_ID: '43' };
  await notify({ env: newEnv, fetchImpl: api.fetchImpl });
  const posts = api.calls.filter(call => call.method === 'POST');
  assert.equal(posts.length, 2);
  assert.match(posts[1].url, /\/issues\/1\/comments$/);
  await notify({ env: newEnv, fetchImpl: api.fetchImpl });
  assert.equal(api.calls.filter(call => call.method === 'POST').length, 2);
});

test('invariant 3: a closed issue prevents a duplicate for the same run', async () => {
  const api = mockApi();
  await notify({ env: env(), fetchImpl: api.fetchImpl });
  const created = api.calls.find(call => call.method === 'POST');
  const closed = { number: 1, state: 'closed', body: created.body.body, user: { login: 'github-actions[bot]' } };
  const retry = mockApi({ issues: [closed] });
  await notify({ env: env(), fetchImpl: retry.fetchImpl });
  assert.equal(retry.calls.filter(call => call.method === 'POST').length, 0);
});

test('invariant 3: scans later pages and their comments before writing', async () => {
  const filler = Array.from({ length: 100 }, (_, index) => ({ number: index + 1, state: 'closed', body: '' }));
  const api = mockApi();
  await notify({ env: env(), fetchImpl: api.fetchImpl });
  const monitored = { number: 101, state: 'open', body: api.calls.find(call => call.method === 'POST').body.body, user: { login: 'github-actions[bot]' } };
  const paged = mockApi({ issues: [...filler, monitored] });
  await notify({ env: { ...env(), GITHUB_RUN_ID: '43' }, fetchImpl: paged.fetchImpl });
  assert.ok(paged.calls.some(call => call.url.includes('page=2')));
  assert.match(paged.calls.find(call => call.method === 'POST').url, /\/issues\/101\/comments$/);
});

test('invariant 3: API failure fails the action before any write', async () => {
  const calls = [];
  const fetchImpl = async (url, options) => {
    calls.push(options?.method ?? 'GET');
    return response({ message: 'rate limited' }, 403);
  };
  await assert.rejects(notify({ env: env(), fetchImpl }), /403/);
  assert.deepEqual(calls, ['GET']);
});

test('invariant 3: finds a retried run on a later comments page of a closed issue', async () => {
  const api = mockApi();
  await notify({ env: env(), fetchImpl: api.fetchImpl });
  const body = api.calls.find(call => call.method === 'POST').body.body;
  const issue = { number: 1, state: 'open', body, user: { login: 'github-actions[bot]' } };
  const comments = { 1: Array.from({ length: 100 }, () => ({ body: 'older run' })) };
  const otherEnv = { ...env(), GITHUB_RUN_ID: '43' };
  const first = mockApi({ issues: [issue], comments });
  await notify({ env: otherEnv, fetchImpl: first.fetchImpl });
  issue.state = 'closed';
  const retry = mockApi({ issues: [issue], comments });
  await notify({ env: otherEnv, fetchImpl: retry.fetchImpl });
  assert.ok(retry.calls.some(call => call.url.includes('/issues/1/comments?per_page=100&page=2')));
  assert.equal(retry.calls.filter(call => call.method === 'POST').length, 0);
});

test('invariant 3: failed comment creation rejects so a retry can append', async () => {
  const api = mockApi();
  await notify({ env: env(), fetchImpl: api.fetchImpl });
  const body = api.calls.find(call => call.method === 'POST').body.body;
  const issue = { number: 1, state: 'open', body, user: { login: 'github-actions[bot]' } };
  const otherEnv = { ...env(), GITHUB_RUN_ID: '43' };
  const retryApi = mockApi({ issues: [issue] });
  const failed = async (url, options = {}) => {
    if (options.method === 'POST') return response({ message: 'failed' }, 503);
    return retryApi.fetchImpl(url, options);
  };
  await assert.rejects(notify({ env: otherEnv, fetchImpl: failed }), /503/);
  await notify({ env: otherEnv, fetchImpl: retryApi.fetchImpl });
  assert.equal(retryApi.calls.filter(call => call.method === 'POST').length, 1);
});


test('invariant 3: ignores a user-created issue with the monitor marker', async () => {
  const api = mockApi();
  await notify({ env: env(), fetchImpl: api.fetchImpl });
  const body = api.calls.find(call => call.method === 'POST').body.body;
  const forged = { number: 1, state: 'open', body, user: { login: 'someone-else' } };
  const fresh = mockApi({ issues: [forged] });
  await notify({ env: env(), fetchImpl: fresh.fetchImpl });
  assert.equal(fresh.calls.filter(call => call.method === 'POST').length, 1);
  assert.equal(fresh.calls.find(call => call.method === 'POST').url.endsWith('/issues'), true);
});

test('invariant 3: ignores a user comment that forges this run marker', async () => {
  const api = mockApi();
  await notify({ env: env(), fetchImpl: api.fetchImpl });
  const body = api.calls.find(call => call.method === 'POST').body.body;
  const oldIssue = { number: 1, state: 'open', body, user: { login: 'github-actions[bot]' } };
  const otherEnv = { ...env(), GITHUB_RUN_ID: '43' };
  const fakeRun = '<!-- peg-hs-lsp-median-run:43:' + baseEnv.GITHUB_SHA + ' -->';
  const fresh = mockApi({ issues: [oldIssue], comments: { 1: [{ body: fakeRun, user: { login: 'someone-else' } }] } });
  await notify({ env: otherEnv, fetchImpl: fresh.fetchImpl });
  assert.equal(fresh.calls.filter(call => call.method === 'POST').length, 1);
});

test('invariant 2: issue records a small threshold exceedance without rounding it to 16.000 ms', async () => {
  const api = mockApi();
  await notify({ env: env([{ ...exceeded[0], seconds: 0.0160001 }]), fetchImpl: api.fetchImpl });
  const body = api.calls.find(call => call.method === 'POST').body.body;
  assert.match(body, /16\.0001/);
});
