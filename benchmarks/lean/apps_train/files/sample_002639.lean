It's 3AM and you get the dreaded call from a customer: the program your company sold them is hanging. You eventually trace the problem down to a call to a function named `mystery`. Usually, `mystery` works fine and produces an integer result for an integer input. However, on certain inputs, the `mystery` function just locks up.

Unfortunately, the `mystery` function is part of a third-party library, and you don't have access to the source code. Uck. It may take a while to get support from the provider of the library, and in the meantime, your customer is getting frustrated.

Your mission, should you choose to accept it, is to create a new function called `wrap_mystery` that returns the same results as `mystery`, but does not hang. Since you're not sure exactly what values `mystery` should be returning for hangs, just have `wrap_mystery` return -1 for problematic input. Your customer is counting on you!

`wrap_mystery` will only be called with positive integers less than 1,000,000.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded
