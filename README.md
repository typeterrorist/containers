# Containers

This repository contains an Agda development of the theory of containers.

## Installation

This project uses a copy of the
[agda-unimath](https://github.com/UniMath/agda-unimath) library as a submodule.
So if you want to download and compile the code you need to also download the
contents of the submodule. For this you need to clone the repository with the
following command:

```
$ git clone --recurse-submodules git@git.app.uib.no:hott/hott-set-theory.git
```

If you forgot to add the `--recurse-submodules` flag when cloning you can run:

```
$ git submodule update --init
```

inside your cloned repository to download the contents of the submodule.

## Working on the repository

The `agda-unimath` submodule points to a certain commit of the
[agda-unimath](https://git.app.uib.no/hott/agda-unimath) repository. So whenever
there are new changes in the `agda-unimath` repository one needs to first pull
the changes and then commit them in the main project (i.e. tell git to move the
pointer to a newer commit).

We will push changes done in the `agda-unimath` module to the `hott-set-theory`
branch in the `agda-unimath` repository. First we need to check out that branch:

```
$ cd agda-unimath/
$ git checkout hott-set-theory
branch 'hott-set-theory' set up to track 'origin/hott-set-theory'.
Switched to a new branch 'hott-set-theory'
$ cd ..
```

### Pulling changes from submodule remote

You can go into the `agda-unimath` subfolder to pull changes, or you can run:

```
$ git submodule update --remote agda-unimath
```

from the project root. This will fetch and merge changes in the submodule.

You then need to commit these changes to the main project.

### Pulling changes from main project

By default, `git pull` (from the repository root) will only fetch changes in the
submodule, without merging (you would need to also run `git submodule update`).
To also merge the changes in the submodule you should run:

```
$ git pull --recurse-submodules
```

This might be worth making into an alias:

```
$ git config alias.spull 'pull --recurse-submodules'
```

### Pushing changes

In order to push changes in both the main project and in the submodule you
should run:

```
$ git push --recurse-submodules=on-demand
```

This pushes first the changes in the submodule and then the changes in the main
repository. If the push in the submodule fails, then the main project push will
fail.

This might be worth making into an alias:

```
$ git config alias.spush 'push --recurse-submodules=on-demand'
```

More detailed documentation can be found here:
https://git-scm.com/book/en/v2/Git-Tools-Submodules


## License

MIT License
