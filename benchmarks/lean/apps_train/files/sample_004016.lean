You're a statistics professor and the deadline for submitting your students' grades is tonight at midnight. Each student's grade is determined by their mean score across all of the tests they took this semester.

You've decided to automate grade calculation by writing a function `calculate_grade()` that takes a list of test scores as an argument and returns a one character string representing the student's grade calculated as follows:

 * 90% <= mean score <= 100%: `"A"`,
 * 80% <= mean score < 90%: `"B"`,
 * 70% <= mean score < 80%: `"C"`,
 * 60% <= mean score < 70%: `"D"`,
 * mean score < 60%: `"F"`

For example, `calculate_grade([92, 94, 99])` would return `"A"` since the mean score is `95`, and `calculate_grade([50, 60, 70, 80, 90])` would return `"C"` since the mean score is `70`.

Your function should handle an input list of any length greater than zero.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
