Ever since you started work at the grocer, you have been faithfully logging down each item and its category that passes through. One day, your boss walks in and asks, "Why are we just randomly placing the items everywhere? It's too difficult to find anything in this place!" Now's your chance to improve the system, impress your boss, and get that raise!

The input is a comma-separated list with category as the prefix in the form `"fruit_banana"`. Your task is to group each item into the 4 categories `Fruit, Meat, Other, Vegetable` and output a string with a category on each line followed by a sorted comma-separated list of items.

For example, given:

```
"fruit_banana,vegetable_carrot,fruit_apple,canned_sardines,drink_juice,fruit_orange"
```

output:

```
"fruit:apple,banana,orange\nmeat:\nother:juice,sardines\nvegetable:carrot"
```

Assume that:
1. Only strings of the format `category_item` will be passed in
2. Strings will always be in lower case
3. Input will not be empty
4. Category and/or item will not be empty
5. There will be no duplicate items
6. All categories may not have items

def group_groceries (input : String) : String :=
  sorry

inductive Category where
  | fruit : Category
  | meat : Category
  | vegetable : Category
  | other : Category
deriving BEq, Repr

structure GroceryItem where
  category : Category
  name : String
deriving Repr

def isValidCategoryName (name : String) : Bool :=  
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded