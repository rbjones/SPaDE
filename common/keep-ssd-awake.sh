#!/bin/bash
# ~/keep-ssd-awake.sh

SSD_PATH="/Volumes/X10Pro"
WAKE_FILE="$SSD_PATH/.vscode-devcontainer-keepalive"

mkdir -p "$SSD_PATH"

while true; do
  touch "$WAKE_FILE" 2>/dev/null || break  # stops if drive unmounts
  sleep 20
done

echo "SSD unmounted, stopping"