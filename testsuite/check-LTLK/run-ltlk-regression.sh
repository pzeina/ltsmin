#!/usr/bin/env bash

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "${SCRIPT_DIR}/../.." && pwd)"
BIN="${ROOT_DIR}/src/pins2lts-seq/dve2lts-seq"
CASES_FILE="${SCRIPT_DIR}/cases.txt"

if [[ ! -x "${BIN}" ]]; then
    echo "ERROR: binary not found: ${BIN}" >&2
    exit 2
fi

if [[ ! -f "${CASES_FILE}" ]]; then
    echo "ERROR: cases file not found: ${CASES_FILE}" >&2
    exit 2
fi

total=0
passed=0
failed=0

tmp_out="$(mktemp -t ltlk-regression.XXXXXX)"
trap 'rm -f "${tmp_out}"' EXIT

echo "Running LTLK regression suite"
echo "Binary: ${BIN}"
echo

while IFS='|' read -r name model formula expected_exit expected_pattern; do
    [[ -z "${name}" ]] && continue
    [[ "${name:0:1}" == "#" ]] && continue

    total=$((total + 1))

    model_path="${ROOT_DIR}/${model}"
    formula_path="${ROOT_DIR}/${formula}"

    if [[ ! -f "${model_path}" ]]; then
        echo "[FAIL] ${name}: model not found (${model_path})"
        failed=$((failed + 1))
        continue
    fi

    if [[ ! -f "${formula_path}" ]]; then
        echo "[FAIL] ${name}: formula not found (${formula_path})"
        failed=$((failed + 1))
        continue
    fi

    "${BIN}" --ltlk-agents=2 --ltlk "${formula_path}" "${model_path}" >"${tmp_out}" 2>&1
    exit_code=$?

    if [[ "${exit_code}" -ne "${expected_exit}" ]]; then
        echo "[FAIL] ${name}: expected exit ${expected_exit}, got ${exit_code}"
        tail -n 20 "${tmp_out}" | sed 's/^/       /'
        failed=$((failed + 1))
        continue
    fi

    if ! grep -Eq "${expected_pattern}" "${tmp_out}"; then
        echo "[FAIL] ${name}: expected pattern not found: ${expected_pattern}"
        tail -n 20 "${tmp_out}" | sed 's/^/       /'
        failed=$((failed + 1))
        continue
    fi

    echo "[PASS] ${name} (exit=${exit_code})"
    passed=$((passed + 1))
done < "${CASES_FILE}"

echo
echo "Summary: ${passed}/${total} passed, ${failed} failed"

if [[ "${failed}" -ne 0 ]]; then
    exit 1
fi

exit 0
