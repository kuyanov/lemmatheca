#!/usr/bin/env bash
set -euo pipefail

repo_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
python="$repo_dir/.venv/bin/python"
static_dir="/var/www/lemmatheca/static"
service="lemmatheca.service"

fail() {
    printf 'Error: %s\n' "$*" >&2
    exit 1
}

if (( EUID == 0 )); then
    fail 'Run ./update_static.sh as your deployment user; it invokes sudo when needed.'
fi

[[ -x "$python" ]] || fail "Python environment missing: $python"
for dependency in rsync sudo systemctl; do
    command -v "$dependency" >/dev/null || fail "Required command missing: $dependency"
done

# Check the service using its command-specific sudo policy. A separate `sudo -v`
# can require a password even when individual commands allow passwordless sudo.
sudo systemctl cat "$service" >/dev/null

printf 'Collecting static files...\n'
"$python" "$repo_dir/app/manage.py" collectstatic --clear --noinput

printf 'Publishing static files to %s...\n' "$static_dir"
sudo install -d -m 755 "$static_dir"
# Remove obsolete assets only after transferring the current collection.
sudo rsync -rtp --delete-after --chmod=Du=rwx,Dgo=rx,Fu=rw,Fgo=r -- \
    "$repo_dir/staticfiles/" "$static_dir/"

printf 'Restarting %s...\n' "$service"
sudo systemctl restart "$service"
sudo systemctl is-active --quiet "$service"
printf 'Static files updated; %s is active.\n' "$service"
