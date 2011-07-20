add_executable(glucose
    Solver.C
    Main.C
)

target_link_libraries(glucose
    ${ZLIB_LIBRARY}
)
