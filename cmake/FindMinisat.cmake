# Find Minisat

set(MINISAT_ROOT "" CACHE PATH "Root of Minisat installation.")

find_path(MINISAT_INCLUDE_DIR NAMES minisat/core/Solver.h PATHS ${MINISAT_ROOT}/include)
find_library(MINISAT_LIBRARY  NAMES minisat  PATHS ${MINISAT_ROOT}/lib)

include (FindPackageHandleStandardArgs)
find_package_handle_standard_args(Minisat
  REQUIRED_VARS MINISAT_LIBRARY MINISAT_INCLUDE_DIR)

mark_as_advanced(MINISAT_LIBRARY MINISAT_INCLUDE_DIR)