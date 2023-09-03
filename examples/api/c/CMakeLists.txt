set(EXAMPLES_BIN_DIR ${CMAKE_BINARY_DIR}/bin/examples/api/c)

macro(btor_add_example name src_files output_dir)
  if("${src_files}" STREQUAL "")
    set(src_files_list ${name}.${file_ext})
  else()
    string(REPLACE " " ";" src_files_list "${src_files}")
  endif()
  add_executable(${name} EXCLUDE_FROM_ALL ${src_files_list})
  target_link_libraries(${name} boolector ${LIBRARIES})
  set(example_bin_dir ${EXAMPLES_BIN_DIR}/${output_dir})
  set_target_properties(${name}
    PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${example_bin_dir})
endmacro()

# array examples
btor_add_example(array1 array/array1.c array)
btor_add_example(array2 array/array2.c array)
btor_add_example(array3 array/array3.c array)

# binarysearch example
btor_add_example(binarysearch binarysearch/binarysearch.c binarysearch)

# boundsprop examples
btor_add_example(minor
  "boundsprop/minor.c boundsprop/minormain.c" boundsprop)
btor_add_example(maxor
  "boundsprop/maxor.c boundsprop/maxormain.c" boundsprop)
btor_add_example(minand
  "boundsprop/minand.c boundsprop/minandmain.c" boundsprop)
btor_add_example(maxand
  "boundsprop/maxand.c boundsprop/maxandmain.c" boundsprop)
btor_add_example(minxor
  "boundsprop/minxor.c boundsprop/minxormain.c" boundsprop)
btor_add_example(maxxor
  "boundsprop/maxxor.c boundsprop/maxxormain.c" boundsprop)

add_executable(theorems EXCLUDE_FROM_ALL boundsprop/theorems.c boundsprop/minor.c
  boundsprop/minand.c boundsprop/maxor.c boundsprop/maxand.c
  boundsprop/minxor.c boundsprop/maxxor.c)
target_link_libraries(theorems boolector ${LIBRARIES})

# bubblesort example
btor_add_example(bubblesort bubblesort/bubblesort.c bubblesort)

# bubblesortmem example
btor_add_example(bubblesortmem bubblesortmem/bubblesortmem.c bubblesortmem)

# bv examples
btor_add_example(bv1 bv/bv1.c bv)
btor_add_example(bv2 bv/bv2.c bv)

# doublereversearray example
btor_add_example(doublereversearray
  doublereversearray/doublereversearray.c doublereversearray)

# ispowerof2 example
btor_add_example(ispowerof2 ispowerof2/ispowerof2.c ispowerof2)

# linearsearch example
btor_add_example(linearsearch linearsearch/linearsearch.c linearsearch)

# matrixmultass example
btor_add_example(matrixmultass matrixmultass/matrixmultass.c matrixmultass)

# matrixmultcomm example
btor_add_example(matrixmultcomm matrixmultcomm/matrixmultcomm.c matrixmultcomm)

# max example
btor_add_example(max max/max.c max)

# memcpy example
btor_add_example(memcpy memcpy/memcpy.c memcpy)

# nextpowerof2 example
btor_add_example(nextpowerof2 nextpowerof2/nextpowerof2.c nextpowerof2)

# selectionsort example
btor_add_example(selectionsort selectionsort/selectionsort.c selectionsort)

# selectionsortmem example
btor_add_example(selectionsortmem
  selectionsortmem/selectionsortmem.c selectionsortmem)

# sudoku example
btor_add_example(sudoku sudoku/sudoku.c sudoku)

# swapmem example
btor_add_example(swapmem swapmem/swapmem.c swapmem)

# exception example
btor_add_example(exception exception.cpp "")

# quickstart example
btor_add_example(quickstart quickstart.c "")

# build all examples at once
add_custom_target(examples
  DEPENDS
  array1
  array2
  array3
  binarysearch
  minor
  maxor
  minand
  maxand
  minxor
  maxxor
  theorems
  bubblesort
  bubblesortmem
  bv1
  bv2
  doublereversearray
  ispowerof2
  linearsearch
  matrixmultass
  matrixmultcomm
  max
  memcpy
  nextpowerof2
  selectionsort
  selectionsortmem
  sudoku
  swapmem
  exception
  quickstart
)
