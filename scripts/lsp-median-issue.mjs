const issueMarker = '<!-- peg-hs-lsp-median-monitor -->';

function required(env, key) {
  const value = env[key];
  if (!value) throw new Error(`${key} is required`);
  return value;
}

function checkedInput(env) {
  const rows = JSON.parse(required(env, 'EXCEEDED'));
  if (!Array.isArray(rows)) throw new Error('EXCEEDED must be an array');
  for (const row of rows) {
    if (typeof row?.grammar !== 'string' || !row.grammar ||
        typeof row.name !== 'string' || !row.name ||
        typeof row.seconds !== 'number' || !Number.isFinite(row.seconds) || row.seconds <= 0.016) {
      throw new Error('EXCEEDED contains an invalid case');
    }
  }
  return rows;
}

function markdown(value) {
  return value.replaceAll('|', '\\|').replaceAll(/[\r\n]/g, ' ');
}

function record(rows, env, runMarker) {
  const server = required(env, 'GITHUB_SERVER_URL').replace(/\/$/, '');
  const repository = required(env, 'GITHUB_REPOSITORY');
  const runId = required(env, 'GITHUB_RUN_ID');
  const sha = required(env, 'GITHUB_SHA');
  return [
    runMarker,
    `CI run [${runId}](${server}/${repository}/actions/runs/${runId}) for commit \`${sha}\` exceeded 16 ms.`,
    '',
    '| Grammar | Edit | Median (ms) |',
    '| --- | --- | ---: |',
    ...rows.map(({ grammar, name, seconds }) =>
      `| ${markdown(grammar)} | ${markdown(name)} | ${String(seconds * 1000)} |`),
  ].join('\n');
}

function apiFor(env) {
  const server = required(env, 'GITHUB_SERVER_URL').replace(/\/$/, '');
  const repository = required(env, 'GITHUB_REPOSITORY');
  if (!/^[^/]+\/[^/]+$/.test(repository)) throw new Error('GITHUB_REPOSITORY is invalid');
  const base = server === 'https://github.com' ? 'https://api.github.com' : `${server}/api/v3`;
  return `${base}/repos/${repository}`;
}

export async function notify({ env = process.env, fetchImpl = fetch } = {}) {
  const rows = checkedInput(env);
  if (rows.length === 0) return;

  const runId = required(env, 'GITHUB_RUN_ID');
  const sha = required(env, 'GITHUB_SHA');
  if (!/^\d+$/.test(runId) || !/^[0-9a-f]{40}$/.test(sha)) throw new Error('Invalid run ID or commit');
  const token = required(env, 'GITHUB_TOKEN');
  const api = apiFor(env);
  const runMarker = `<!-- peg-hs-lsp-median-run:${runId}:${sha} -->`;
  const body = record(rows, env, runMarker);
  const headers = {
    Accept: 'application/vnd.github+json',
    Authorization: `Bearer ${token}`,
    'Content-Type': 'application/json',
    'X-GitHub-Api-Version': '2022-11-28',
  };

  async function request(path, options = {}) {
    const response = await fetchImpl(`${api}${path}`, { ...options, headers });
    if (!response.ok) throw new Error(`GitHub API returned ${response.status} for ${path}`);
    return response.json();
  }

  async function pages(path) {
    const all = [];
    for (let page = 1; ; page++) {
      const batch = await request(`${path}${path.includes('?') ? '&' : '?'}per_page=100&page=${page}`);
      if (!Array.isArray(batch)) throw new Error('GitHub API returned a non-array page');
      all.push(...batch);
      if (batch.length < 100) return all;
    }
  }

  const issues = (await pages('/issues?state=all')).filter(issue =>
    !issue.pull_request && issue.user?.login === 'github-actions[bot]' &&
    typeof issue.body === 'string' && issue.body.includes(issueMarker));
  for (const issue of issues) {
    if (issue.body.includes(runMarker)) return;
    const comments = await pages(`/issues/${issue.number}/comments`);
    if (comments.some(comment => comment.user?.login === 'github-actions[bot]' &&
      comment.body?.includes(runMarker))) return;
  }

  const open = issues.find(issue => issue.state === 'open');
  if (open) {
    await request(`/issues/${open.number}/comments`, {
      method: 'POST', body: JSON.stringify({ body }),
    });
    return;
  }
  await request('/issues', {
    method: 'POST',
    body: JSON.stringify({ title: 'peg-hs LSP latency exceeded 16 ms in CI', body: `${issueMarker}\n${body}` }),
  });
}

if (import.meta.main) {
  await notify();
}
