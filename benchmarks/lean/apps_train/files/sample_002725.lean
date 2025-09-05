Alan's child can be annoying at times.

When Alan comes home and tells his kid what he has accomplished today, his kid never believes him. 

Be that kid.

Your function 'AlanAnnoyingKid' takes as input a sentence spoken by Alan (a string). The sentence contains the following structure:

    "Today I " + [action_verb] + [object] + "."

    (e.g.: "Today I played football.")

Your function will return Alan's kid response, which is another sentence with the following structure:

    "I don't think you " + [action_performed_by_alan] + " today, I think you " + ["did" OR "didn't"] + [verb_of _action_in_present_tense] + [" it!" OR " at all!"]

    (e.g.:"I don't think you played football today, I think you didn't play at all!")

Note the different structure depending on the presence of a negation in Alan's first sentence (e.g., whether Alan says "I dind't play football", or "I played football").

! Also note: Alan's kid is young and only uses simple, regular verbs that use a simple "ed" to make past tense. 
There are random test cases.

Some more examples:

    input  = "Today I played football."
    output = "I don't think you played football today, I think you didn't play at all!"

    input  = "Today I didn't attempt to hardcode this Kata."
    output = "I don't think you didn't attempt to hardcode this Kata today, I think you did attempt it!"

    input  = "Today I didn't play football."
    output = "I don't think you didn't play football today, I think you did play it!"

    input  = "Today I cleaned the kitchen."
    output = "I don't think you cleaned the kitchen today, I think you didn't clean at all!"

def String.substringExists (s : String) (sub : String) : Bool := sorry

def alan_annoying_kid (phrase : String) : String := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded