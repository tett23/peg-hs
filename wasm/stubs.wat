;; The functions of wasi_snapshot_preview1 that the build imports outside
;; the import contract of ADR 0078 (ADR 0079). scripts/build-wasm.sh merges
;; this module into the build as wasi_snapshot_preview1, so the imports
;; become these functions. Each one reads no argument and returns an errno
;; at once: EBADF (8) from fd_prestat_get, since no directory is preopened,
;; and ENOSYS (52) from the others. The types are those of WASI preview1.
(module
  (func (export "fd_close") (param i32) (result i32) i32.const 52)
  (func (export "fd_fdstat_get") (param i32 i32) (result i32) i32.const 52)
  (func (export "fd_fdstat_set_flags") (param i32 i32) (result i32) i32.const 52)
  (func (export "fd_filestat_get") (param i32 i32) (result i32) i32.const 52)
  (func (export "fd_filestat_set_size") (param i32 i64) (result i32) i32.const 52)
  (func (export "fd_prestat_get") (param i32 i32) (result i32) i32.const 8)
  (func (export "fd_prestat_dir_name") (param i32 i32 i32) (result i32) i32.const 52)
  (func (export "fd_read") (param i32 i32 i32 i32) (result i32) i32.const 52)
  (func (export "fd_seek") (param i32 i64 i32 i32) (result i32) i32.const 52)
  (func (export "path_create_directory") (param i32 i32 i32) (result i32) i32.const 52)
  (func (export "path_filestat_get") (param i32 i32 i32 i32 i32) (result i32) i32.const 52)
  (func (export "path_open") (param i32 i32 i32 i32 i32 i64 i64 i32 i32) (result i32) i32.const 52)
  (func (export "poll_oneoff") (param i32 i32 i32 i32) (result i32) i32.const 52))
