<!--
  vim: filetype=markdown
-->

[![Build Status][build-status-badge]][build-status-link]
[![Ready Stories][tickets-badge]][tickets-link]
[build-status-badge]: https://travis-ci.org/waylang/infrastructure.svg?branch=master
[build-status-link]: https://travis-ci.org/waylang/infrastructure
[tickets-badge]: https://badge.waffle.io/waylang/infrastructure.png?label=ready&title=Ready
[tickets-link]: http://waffle.io/waylang/infrastructure

# Infrastructure
Cross-repository Services

## About

Infrastructure's goal is to keep the Way development environments consistent across the repositories of the organization.  It aims to do so by moving common aspects of their provisioning to a single place.  Hand in hand with this goal is automating common life cycle tasks, including creating a new repository in the organization.

In organiaztion repositories there is a natural tension between similarity (for a portable developer experience) and diversity (for achieving required function).  Infrastructure takes the following stance:
* All repositories will avoid a thick host OS tool chain by sand-boxing development within [vagrant][vagrant].
* All repositories will automate development environment provisioning with bash.
* Infrastructure will clearly divide maintenance responsibility of common files, and all repositories will respect this division.

The first point seeks to limit host OS dependencies to:
* `bash`
* `gpg` or `gpg2` (only needed to tag releases)
* `git`
* `vagrant`
* [`virtualbox`][virtualbox]
* your text editor of choice

The goal of the last point is to avoid code rot introduced by projects being created at various times in the face of evolving project templates.  When a significantly complex file changes in a way that all repositories should consume, infrastructure will roll the change out, e.g. as an updated template.

Infrastructure makes an effort to allow client repositories to retain ownership of most files.  Infrastructure implements two strategies for managing the portions of those files that it owns.  First, it tries to offer an inclusion mechanism of some sort.  When inclusion is not appropriate, it falls back to validating client-owned files during test to ensure that required features are present (see `layout.bats`).

Infrastructure explicitly does not:
* Require a particular host OS (in theory)
* Require an editor, though [editorconfig][editorconfig] users will benefit.
* Require or automate the configuration of external services such as continuous integration.

[vagrant]: https://www.vagrantup.com/
[virtualbox]: https://www.virtualbox.org/
[editorconfig]: http://editorconfig.org/

## Creating a new Repository

First, make a new way repository in the Github UI.  Then:

```
git clone git@github.com:waylang/new_repo.git
cd new_repo
curl -s https://raw.githubusercontent.com/waylang/infrastructure/master/install | bash
```

This fetches the latest [github release][github-releases] of infrastructure, which generates a `Vagrantfile` and drops into provisioning to create the rest of the project template.  You will be left with some files to commit in your staging area, and a running vagrant instance.

[github-releases]: https://help.github.com/articles/about-releases/

## Releasing a new Version

On the _host_ OS, use `./bin/bump-version` with `major`, `minor` or `patch` arguments to bump the given semantic version component.  This will modify the `version` file in a new commit and add a gpg-signed, annotated tag.  Neither the commit nor the tag is not automatically pushed.

It is expected that the repository's CI service will trigger a build in response to pushing the tag and, if the build succeeds, release the new version using the appropriate continuous delivery process.

## License

Copyright (C) 2016-2017 Philip H. Smith

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.
