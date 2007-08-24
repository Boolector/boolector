#ifndef TESTRUNNER_H_INCLUDED
#define TESTRUNNER_H_INCLUDED

#define BTOR_RUN_TEST_CHECK_LOG(name) \
  run_test_case (argc, argv, test_##name, #name, 1)

#define BTOR_RUN_TEST(name) run_test_case (argc, argv, test_##name, #name, 0)

enum BtorTestCaseSpeed
{
  BTOR_FAST_TEST_CASE   = 0,
  BTOR_NORMAL_TEST_CASE = 1,
  BTOR_SLOW_TEST_CASE   = 2,
};

typedef enum BtorTestCaseSpeed BtorTestCaseSpeed;

void init_tests (BtorTestCaseSpeed speed);

void print_test_suite_name (const char *name);

void run_test_case (
    int argc, char **argv, void (*funcp) (), char *name, int check_log_file);

void finish_tests (void);

#endif
