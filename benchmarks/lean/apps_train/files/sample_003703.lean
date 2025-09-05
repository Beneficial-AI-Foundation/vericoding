Your Goal is to create a function that takes  two strings, a guess and a phone number. 

Based on the guess, the function should display a portion of the phone number:

    guess_my_number('052', '123-451-2345')
    would return the string: '#2#-#5#-2##5'

    or

    guess_my_number('142', '123-451-2345')
    would return the string: '12#-4#1-2#4#'

Order of the guess string should not matter, and should not have duplicates of the ten digitis 0-9. Guess will never be an empty string or contains any other charachters. The phone number will always bea ten digit number in the format ###-###-####.

The default number of 123-451-2345 should be included, but can be overwriten by a different number if supplied at the time of execution.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded
