# Pikelet!

![Pikelet Mascot][pikelet-mascot]

[pikelet-mascot]: assets/pikelet.png

[![Actions Status][actions-badge]][actions-url]
[![Matrix][matrix-badge]][matrix-lobby]
[![License][license-badge]][license-url]

[actions-badge]: https://github.com/pikelet-lang/pikelet/workflows/Continuous%20integration/badge.svg
[actions-url]: https://github.com/pikelet-lang/pikelet/actions
[matrix-badge]: https://img.shields.io/matrix/pikelet:matrix.org?label=%23pikelet%3Amatrix.org
[matrix-lobby]: https://app.element.io/#/room/#pikelet:matrix.org
[license-badge]: https://img.shields.io/github/license/pikelet-lang/pikelet
[license-url]: ./LICENSE
[code-of-conduct-badge]: https://img.shields.io/badge/Contributor%20Covenant-v2.0%20adopted-ff69b4.svg
[code-of-conduct-url]: ./CODE_OF_CONDUCT.md

Pikelet is a small, functional, dependently typed programming language.

Dependent types allow us to do a bunch of really interesting things, like using
records for modules, declaring the length of arrays at the type level, and
much more — many of great utility for low-level and high-level code alike!

We hope to one day grow Pikelet into fully-fledged systems programming language,
with support for unboxed data types, control over memory layout and allocation
strategy, linear types, and a flexible phase distinction and support for calling
other languages. At the moment however we've only implemented a type checker and
very slow  interpreter, so don't get your hopes up too much yet! There's still a
whole lot to do before it is even remotely useful to anyone! 😅

## Roadmap

Check out our plans in [the roadmap](./website/docs/contributing/roadmap.md).

## Code of Conduct

Please note that this project is released with a [Code of Conduct](./CODE_OF_CONDUCT.md).
By participating in this project you agree to abide by its terms.
