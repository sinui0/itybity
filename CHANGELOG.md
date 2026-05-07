# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.3.3] - 2026-05-07
### Added
- `SetBit` trait for indexed bit assignment, implemented for all integer primitives and `bool`.

### Changed
- Documented `FromBitIterator` behavior when the input iterator is longer or shorter than the target type.
- Expanded crate-level feature documentation to cover `alloc` and `rayon`.
- `StrBitIter` now implements `FusedIterator`.

### Fixed
- Stale references to a `FromBits` trait in the README (the trait is `FromBitIterator`).
- Stale `itybity = "0.1"` version in the crate-level usage example.

## [0.3.2] - 2026-04-23
### Added
- `GetBit` and `FromBitIterator` implementations for signed integer primitives (`i8`, `i16`, `i32`, `i64`, `i128`, `isize`).
- Rayon tests.

## [0.3.1] - 2025-03-14
### Added
- `FromBitIterator` implementation for `bool`.

## [0.3.0] - 2025-03-14
### Added
- `FromBitIterator` implementation for tuples.
- `ToBits` implementation for primitive arrays.
- `rayon` feature providing parallel bit iterators.

### Changed
- Loosened `rayon` version requirement.
- Bumped `rstest` dev-dependency.

## [0.2.1] - 2023-07-21
### Fixed
- `no_std` build (#10).

### Changed
- Bumped `rstest` dev-dependency.

## [0.2.0] - 2023-07-05
### Added
- `rayon` support.

### Changed
- Major API simplification: blanket implementations of `GetBit`, `BitLength`, and related traits.
- Relaxed `Clone` and `Sized` bounds across the public surface.

## [0.1.6] - 2023-06-17
### Added
- `GetBit` implementation for `Vec`.

### Removed
- `ToBits` implementation for `Vec<bool>` (#6).

## [0.1.5] - 2023-06-17
### Changed
- Documentation updates.

## [0.1.4] - 2023-06-17
### Added
- `FromBits` implementations for `Vec` and arrays (#5).

## [0.1.3] - 2023-06-16
### Added
- `GetBit` implementation for `bool` (#4).

## [0.1.2] - 2023-06-16
### Added
- Blanket implementations for `GetBit` (#3).

## [0.1.1] - 2023-06-16
### Added
- `BitLength` implementations for `bool` and arrays (#2).

## [0.1.0] - 2023-06-04
### Added
- Initial release.

[Unreleased]: https://github.com/sinui0/itybity/compare/0.3.3...HEAD
[0.3.3]: https://github.com/sinui0/itybity/compare/0.3.2...0.3.3
[0.3.2]: https://github.com/sinui0/itybity/compare/0.3.1...0.3.2
[0.3.1]: https://github.com/sinui0/itybity/compare/0.3.0...0.3.1
[0.3.0]: https://github.com/sinui0/itybity/compare/0.2.1...0.3.0
[0.2.1]: https://github.com/sinui0/itybity/compare/0.2.0...0.2.1
[0.2.0]: https://github.com/sinui0/itybity/compare/0.1.6...0.2.0
[0.1.6]: https://github.com/sinui0/itybity/compare/0.1.5...0.1.6
[0.1.5]: https://github.com/sinui0/itybity/compare/0.1.4...0.1.5
[0.1.4]: https://github.com/sinui0/itybity/compare/0.1.3...0.1.4
[0.1.3]: https://github.com/sinui0/itybity/compare/0.1.2...0.1.3
[0.1.2]: https://github.com/sinui0/itybity/compare/0.1.1...0.1.2
[0.1.1]: https://github.com/sinui0/itybity/compare/0.1.0...0.1.1
[0.1.0]: https://github.com/sinui0/itybity/releases/tag/0.1.0
