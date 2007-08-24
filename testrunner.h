#ifndef TESTRUNNER_H_INCLUDED
#define TESTRUNNER_H_INCLUDED

#define BTOR_RUN_TEST_CHECK_LOG(name) \
  run_test_case (argc, argv, test_##name, #name, 1)

#define BTOR_RUN_TEST(name) run_test_case (argc, argv, test_##name, #name, 0)

void init_tests (int fast);

void print_test_suite_name (const char *name);

void run_test_case (
    int argc, char **argv, void (*funcp) (), char *name, int check_log_file);

void finish_tests (void);

#endif
