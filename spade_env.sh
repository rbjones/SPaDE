# Source this file: . ./spade_env.sh
SPADEHOME=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
export SPADEHOME

# Drop entries for any other SPaDE worktree, then prepend this one.
newpath=
IFS=: read -ra parts <<< "$PPDATABASEPATH"
for p in "${parts[@]}"; do
  case $p in "$HOME"/git/SPaDE-*) ;; *) newpath=${newpath:+$newpath:}$p ;; esac
done
export PPDATABASEPATH="$SPADEHOME${newpath:+:$newpath}"