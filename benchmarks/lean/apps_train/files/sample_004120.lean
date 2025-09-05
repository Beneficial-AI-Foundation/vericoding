You will be given a fruit which a farmer has harvested, your job is to see if you should buy or sell.

You will be given 3 pairs of fruit. Your task is to trade your harvested fruit back into your harvested fruit via the intermediate pair, you should return a string of 3 actions.

if you have harvested apples, you would buy this fruit pair: apple_orange, if you have harvested oranges, you would sell that fruit pair.

(In other words, to go from left to right (apples to oranges) you buy, and to go from right to left you sell (oranges to apple))

e.g. 
apple_orange, orange_pear, apple_pear
1. if you have harvested apples, you would buy this fruit pair: apple_orange
2. Then you have oranges, so again you would buy this fruit pair: orange_pear
3. After you have pear, but now this time you would sell this fruit pair: apple_pear
4. Finally you are back with the apples

So your function would return a list: [“buy”,”buy”,”sell”]

If any invalid input is given, "ERROR" should be returned

def is_valid_path (pairs : List (List String)) (start : String) (actions : Result String) : Bool :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded
