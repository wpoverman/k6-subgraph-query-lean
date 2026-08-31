# Publishing this project on GitHub

The simplest route uses the GitHub CLI. Run these commands from the project
directory after choosing the repository name and whether it should be public.

```sh
lake build
lake exe verify-k6-prefix

git init
git add .
git commit -m "Formalize the K6 subgraph-query theorem"
git branch -M main

gh auth login
gh repo create k6-subgraph-query-lean --public --source=. --remote=origin --push
```

The `.gitignore` already excludes `.lake/`, so compiled dependencies and build
artifacts are not committed. Do not add the generated `.lake` directory or a
Lean toolchain installation to Git.

Before making the repository public, decide on a license and add the
corresponding `LICENSE` file. Also replace any draft repository URL in the
paper only after GitHub reports the final URL.

If the destination repository already exists, do not run `gh repo create`.
Instead inspect `git remote -v`, add the exact remote only if it is absent,
and push without force:

```sh
git remote add origin https://github.com/OWNER/REPOSITORY.git
git push -u origin main
```

## Prompt for Codex

If Codex is running in this directory and GitHub authentication is already
configured, the following is a suitable instruction:

> Check that the Lean project builds and that no generated `.lake` files are
> tracked. Initialize a Git repository if needed, commit the source and
> documentation, create a new public GitHub repository named
> `k6-subgraph-query-lean` under my authenticated account, and push the main
> branch. Do not force-push, overwrite an existing remote, publish secrets, or
> choose a software license without asking me. Return the repository URL and
> the exact verification commands you ran.

If a repository already exists, give Codex its exact URL and ask it to inspect
the current remotes and branch before changing anything.
