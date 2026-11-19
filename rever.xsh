# SPDX-License-Identifier: GPL-3.0-or-later
# Release script for rever (https://regro.github.io/rever-docs/): `rever <version>`.

import sys

try:
  input("Are you sure you are on the main branch which is identical to origin/main? [ENTER]")
except KeyboardInterrupt:
  sys.exit(1)

from rever.activities.command import command

tarball_name = 'dist/cubic_twostage-' + $VERSION + '.tar.gz'
command('build', 'python -m build --sdist')
command('twine', ''.join(['twine upload ', tarball_name]))

$GITHUB_CREDFILE = '~/.git-credentials'
$PROJECT = 'cubic_twostage'

$ACTIVITIES = [
    'version_bump',
    'changelog',
    'build',
    'twine',
    'tag',
    'push_tag',
    'ghrelease',
]

$VERSION_BUMP_PATTERNS = [
  ('pyproject.toml', r"version =", 'version = "$VERSION"'),
  ('doc/conf.py', r"release =", 'release = "$VERSION"'),
  ('cubic_twostage/__init__.py', r"__version__ =", '__version__ = "$VERSION"'),
]

$CHANGELOG_FILENAME = 'ChangeLog'
$CHANGELOG_TEMPLATE = 'TEMPLATE.rst'
$CHANGELOG_NEWS = 'doc/news'
$PUSH_TAG_REMOTE = 'git@github.com:mmasdeu/cubic_twostage.git'

$GITHUB_ORG = 'mmasdeu'
$GITHUB_REPO = 'cubic_twostage'

$GHRELEASE_ASSETS = [tarball_name]
