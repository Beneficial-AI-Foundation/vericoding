Mr. Khalkhoul, an amazing teacher, likes to answer questions sent by his students via e-mail, but he often doesn't have the time to answer all of them. In this kata you will help him by making a program that finds
some of the answers.

You are given a `question` which is a string containing the question and some `information` which is a list of strings representing potential answers.

Your task is to find among `information` the UNIQUE string that has the highest number of words in common with `question`. We shall consider words to be separated by a single space.

You can assume that:

* all strings given contain at least one word and have no leading or trailing spaces,
* words are composed with alphanumeric characters only

You must also consider the case in which you get no matching words (again, ignoring the case): in such a case return `None/nil/null`.

Mr. Khalkhoul is countin' on you :)

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded