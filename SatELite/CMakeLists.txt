include_directories( ${PROJECT_SOURCE_DIR}/SatELite/ForMani )

add_executable(satelite
    SatElite/BcnfWriter.C
    SatElite/Main.C
    SatElite/Main_debug.C
    SatElite/Profile.C
    SatElite/Solver.C
    SatElite/Solver_clause.C
    SatElite/Solver_debug.C
    SatElite/Solver_subsume.C
    SatElite/TmpFiles.C
    ForMani/File.C
    ForMani/Global.C
    ForMani/String.C
)

target_link_libraries(satelite
    ${ZLIB_LIBRARY}
)
