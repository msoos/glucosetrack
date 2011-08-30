add_executable(glucose_track
    Solver.C
    Main.C
)

target_link_libraries(glucose_track
    ${ZLIB_LIBRARY}
)

