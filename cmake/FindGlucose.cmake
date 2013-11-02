# Find Glucose

set(GLUCOSE_ROOT "" CACHE PATH "Root of Glucose installation.")

find_path(GLUCOSE_INCLUDE_DIR NAMES core/Solver.h PATHS ${GLUCOSE_ROOT}/include/glucose)
find_library(GLUCOSE_LIBRARY  NAMES glucose  PATHS ${GLUCOSE_ROOT}/lib)

include (FindPackageHandleStandardArgs)
find_package_handle_standard_args(Glucose
  REQUIRED_VARS GLUCOSE_LIBRARY GLUCOSE_INCLUDE_DIR)

mark_as_advanced(GLUCOSE_LIBRARY GLUCOSE_INCLUDE_DIR)