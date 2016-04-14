[![Build Status][build-status-badge]][build-status-link]
[![Ready Stories][tickets-badge]][tickets-link]
[build-status-badge]: https://travis-ci.org/waylang/infrastructure.svg?branch=master
[build-status-link]: https://travis-ci.org/waylang/infrastructure
[tickets-badge]: https://badge.waffle.io/waylang/infrastructure.png?label=ready&title=Ready
[tickets-link]: http://waffle.io/waylang/infrastructure

# Infrastructure
Cross-repository Services

## About

Infrastructure's goal is to keep the Way development environments consistent across the repos of the organization.  It aims to do so by extracting their provisioning to a single place.  Hand in hand with this goal is automating the process of creating a new repo in the organization.

There is a natural trade-off between similarity (for portable UX) and diversity (for achieving required function) of org repos.  Infrastructure takes the following stance:
* All repos will avoid a thick host OS tool chain by sand-boxing development within vagrant.
* All repos will use ruby and its ecosystem (e.g. rake) for tooling where possible.
* All repos will automate development environment provisioning with chef.
* Infrastructure will clearly divide maintenance responsibility of common files, and all repos will respect this division of responsibility.

The first point seeks to limit host OS dependencies to:
* git
* vagrant
* text editor of choice

The goal of the last point is to avoid code rot introduced by projects being created at various times in the face of evolving project templates.  When a significantly complex file changes in a way that all repos should consume, infrastructure will roll the change out (e.g. as an updated chef template.)

Infrastructure makes an effort to allow client repositories to retain ownership of most files.  Infrastructure implements two strategies for managing the portions of those files that it owns.  First, it tries to offer an inclusion mechanism of some sort either native to the file format or via a chef partial template.  When inclusion is not appropriate, it falls back to validating client-owned files at provision time to ensure that required features are present (see `project_spec.rb`.)

Infrastructure explicitly does not require:
* Committing to a host OS (in theory)
* Committing to an editor, though [editorconfig][editorconfig] users will benefit.
* Committing to or automating the configuration of external services such as travis CI.

[editorconfig]: http://editorconfig.org/

## Creating a new Repository

First, make a new way repo in the Github UI.  Then:

```
git clone git@github.com:waylang/new_repo.git
cd new_repo
curl -s https://raw.githubusercontent.com/waylang/infrastructure/master/install | bash
```

This fetches the latest [github release][github-releases] of infrastructure, which generates a Vagrantfile and drops into chef provisioning to create the rest of the project template.  You will be left with some files to commit in your staging area, and a running vagrant instance.

[github-releases]: https://help.github.com/articles/about-releases/

## Releasing a new Version

Use the `version:major`, `version:minor` and `version:patch` rake tasks to bump the given semantic version component.  This will create a new commit (modifying the `version` file) and an annotated tag.  The tag is not automatically pushed.

It is expected that the repository's CI service will trigger a build in response to pushing the tag and, if the build succeeds, release the new version using the appropriate continuous delivery process.
