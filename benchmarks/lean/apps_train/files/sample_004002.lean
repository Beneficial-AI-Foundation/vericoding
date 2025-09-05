From Wikipedia : "The n-back task is a continuous performance task that is commonly used as an assessment in cognitive neuroscience to measure a part of working memory and working memory capacity. [...] The subject is presented with a sequence of stimuli, and the task consists of indicating when the current stimulus matches the one from n steps earlier in the sequence. The load factor n can be adjusted to make the task more or less difficult."

In this kata, your task is to "teach" your computer to do the n-back task. Specifically, you will be implementing a function that counts the number of "targets" (stimuli that match the one from n steps earlier) in a sequence of digits. Your function will take two parameters :

n, a positive integer equal to the number of steps to look back to find a match
sequence, a sequence of digits containing 0 or more targets

A few hints :

The first digit in a sequence can never be a target
Targets can be "chained" together (e.g., for n = 1 and sequence = [1, 1, 1], there are 2 targets)

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible