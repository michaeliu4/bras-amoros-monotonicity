#!/usr/bin/env bash
# Public dependencies only; no project build cache is restored here.
set -euo pipefail
python3 -I .github/lean/prepare.py
# The disposable hosted runner does not need these unrelated preinstalled SDKs.
sudo rm -rf /usr/share/dotnet /usr/local/lib/android /opt/ghc /opt/hostedtoolcache/CodeQL /usr/local/share/boost
mkdir -p .tools/elan-installer
readarray -t elan_info < <(python3 -c 'import json; d=json.load(open(".github/lean/elan-linux.json")); print(d["url"]); print(d["sha256"])')
curl --fail --location --proto '=https' --tlsv1.2 "${elan_info[0]}" -o .tools/elan.tar.gz
echo "${elan_info[1]}  .tools/elan.tar.gz" | sha256sum --check -
tar -xzf .tools/elan.tar.gz -C .tools/elan-installer
.tools/elan-installer/elan-init -y --no-modify-path --default-toolchain none
"$ELAN_HOME/bin/elan" toolchain install leanprover/lean4:v4.32.1
export PATH="$ELAN_HOME/bin:$PATH"
echo "$ELAN_HOME/bin" >> "$GITHUB_PATH"
# A bounded swap file helps kernel aggregation on standard Linux runners.
if ! swapon --show | grep -q .; then
  sudo fallocate -l 8G /swapfile
  sudo chmod 600 /swapfile
  sudo mkswap /swapfile >/dev/null
  sudo swapon /swapfile
fi
(
  mapfile -t targets < .ci-plan/mathlib-roots.txt
  cd lean
  lean --version
  lake exe cache get "${targets[@]}"
)
python3 -I .github/lean/prepare.py

