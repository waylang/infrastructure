<!--
  vim: fenc=utf-8 ff=unix sts=2 sw=2 et ft=markdown
-->

[![Build Status][build-status-badge]][build-status-link]
[![Ready Stories][tickets-badge]][tickets-link]

[build-status-badge]: https://travis-ci.org/waylang/infrastructure.svg?branch=master
[build-status-link]: https://travis-ci.org/waylang/infrastructure
[tickets-badge]: https://badge.waffle.io/waylang/infrastructure.png?label=ready&title=Ready
[tickets-link]: http://waffle.io/waylang/infrastructure

# Infrastructure

Project Lifecycle and Tooling

## About

Infrastructure provides necessities such as the build, tooling, development environment,
continuous integration and deployment.

It avoids a thick host OS tool chain by sand-boxing development within [vagrant][vagrant].
Host OS dependencies are limited to:
* `bash`
* `gpg` or `gpg2` (only needed to tag releases)
* `git`
* `vagrant`
* [`virtualbox`][virtualbox]
* your text editor of choice

Infrastructure explicitly does not require:
* A particular host OS (in theory, tested on macOS)
* A particular editor, though [editorconfig][editorconfig] users will benefit.

[vagrant]: https://www.vagrantup.com/
[virtualbox]: https://www.virtualbox.org/
[editorconfig]: http://editorconfig.org/

## Releasing a new Version

On the _host_ OS, use `./infrastructure/bin/bump-version` with the desired new version.
This will modify the `version` file in a new commit and add a gpg-signed, annotated tag.
Neither the commit nor the tag is not automatically pushed.

It is expected that continuous integration will trigger a build in response to pushing the
tag and, if the build succeeds, release the new version.

## License

Copyright (C) 2016-2018 Philip H. Smith

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.
