set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin/examples)

# array examples
add_executable(array1 EXCLUDE_FROM_ALL array/array1.c)
target_link_libraries(array1 boolector ${LIBRARIES})

add_executable(array2 EXCLUDE_FROM_ALL array/array2.c)
target_link_libraries(array2 boolector ${LIBRARIES})

add_executable(array3 EXCLUDE_FROM_ALL array/array3.c)
target_link_libraries(array3 boolector ${LIBRARIES})

# binarysearch example
add_executable(binarysearch EXCLUDE_FROM_ALL binarysearch/binarysearch.c)
target_link_libraries(binarysearch boolector ${LIBRARIES})

# boundsprop examples
add_executable(minor EXCLUDE_FROM_ALL boundsprop/minor.c boundsprop/minormain.c)
target_link_libraries(minor boolector ${LIBRARIES})

add_executable(maxor EXCLUDE_FROM_ALL boundsprop/maxor.c boundsprop/maxormain.c)
target_link_libraries(maxor boolector ${LIBRARIES})

add_executable(minand EXCLUDE_FROM_ALL boundsprop/minand.c boundsprop/minandmain.c)
target_link_libraries(minand boolector ${LIBRARIES})

add_executable(maxand EXCLUDE_FROM_ALL boundsprop/maxand.c boundsprop/maxandmain.c)
target_link_libraries(maxand boolector ${LIBRARIES})

add_executable(minxor EXCLUDE_FROM_ALL boundsprop/minxor.c boundsprop/minxormain.c)
target_link_libraries(minxor boolector ${LIBRARIES})

add_executable(maxxor EXCLUDE_FROM_ALL boundsprop/maxxor.c boundsprop/maxxormain.c)
target_link_libraries(maxxor boolector ${LIBRARIES})

add_executable(theorems EXCLUDE_FROM_ALL boundsprop/theorems.c boundsprop/minor.c
  boundsprop/minand.c boundsprop/maxor.c boundsprop/maxand.c
  boundsprop/minxor.c boundsprop/maxxor.c)
target_link_libraries(theorems boolector ${LIBRARIES})

# bubblesort example
add_executable(bubblesort EXCLUDE_FROM_ALL bubblesort/bubblesort.c)
target_link_libraries(bubblesort boolector ${LIBRARIES})

# bubblesortmem example
add_executable(bubblesortmem EXCLUDE_FROM_ALL bubblesortmem/bubblesortmem.c)
target_link_libraries(bubblesortmem boolector ${LIBRARIES})

# bv examples
add_executable(bv1 EXCLUDE_FROM_ALL bv/bv1.c)
target_link_libraries(bv1 boolector ${LIBRARIES})

add_executable(bv2 EXCLUDE_FROM_ALL bv/bv2.c)
target_link_libraries(bv2 boolector ${LIBRARIES})

# doublereversearray example
add_executable(doublereversearray EXCLUDE_FROM_ALL
  doublereversearray/doublereversearray.c)
target_link_libraries(doublereversearray boolector ${LIBRARIES})

# ispowerof2 example
add_executable(ispowerof2 EXCLUDE_FROM_ALL ispowerof2/ispowerof2.c)
target_link_libraries(ispowerof2 boolector ${LIBRARIES})

# linearsearch example
add_executable(linearsearch EXCLUDE_FROM_ALL linearsearch/linearsearch.c)
target_link_libraries(linearsearch boolector ${LIBRARIES})

# matrixmultass example
add_executable(matrixmultass EXCLUDE_FROM_ALL matrixmultass/matrixmultass.c)
target_link_libraries(matrixmultass boolector ${LIBRARIES})

# matrixmultcomm example
add_executable(matrixmultcomm EXCLUDE_FROM_ALL matrixmultcomm/matrixmultcomm.c)
target_link_libraries(matrixmultcomm boolector ${LIBRARIES})

# max example
add_executable(max EXCLUDE_FROM_ALL max/max.c)
target_link_libraries(max boolector ${LIBRARIES})

# memcpy example
add_executable(memcpy EXCLUDE_FROM_ALL memcpy/memcpy.c)
target_link_libraries(memcpy boolector ${LIBRARIES})

# nextpowerof2 example
add_executable(nextpowerof2 EXCLUDE_FROM_ALL nextpowerof2/nextpowerof2.c)
target_link_libraries(nextpowerof2 boolector ${LIBRARIES})

# selectionsort example
add_executable(selectionsort EXCLUDE_FROM_ALL selectionsort/selectionsort.c)
target_link_libraries(selectionsort boolector ${LIBRARIES})

# selectionsortmem example
add_executable(selectionsortmem EXCLUDE_FROM_ALL selectionsortmem/selectionsortmem.c)
target_link_libraries(selectionsortmem boolector ${LIBRARIES})

# sudoku example
add_executable(sudoku EXCLUDE_FROM_ALL sudoku/sudoku.c)
target_link_libraries(sudoku boolector ${LIBRARIES})

# swapmem example
add_executable(swapmem EXCLUDE_FROM_ALL swapmem/swapmem.c)
target_link_libraries(swapmem boolector ${LIBRARIES})

# exception example
add_executable(exception EXCLUDE_FROM_ALL exception.cpp)
target_link_libraries(exception boolector ${LIBRARIES})

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
)
