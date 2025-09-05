A carpet shop sells carpets in different varieties. Each carpet can come in a different roll width and can have a different price per square meter. 

Write a function `cost_of_carpet` which calculates the cost (rounded to 2 decimal places) of carpeting a room, following these constraints:

* The carpeting has to be done in one unique piece. If not possible, retrun `"error"`.
* The shop sells any length of a roll of carpets, but always with a full width.
* The cost has to be minimal.
* The length of the room passed as argument can sometimes be shorter than its width (because we define these relatively to the position of the door in the room).
* A length or width equal to zero is considered invalid, return `"error"` if it occurs.

INPUTS:

`room_width`, `room_length`, `roll_width`, `roll_cost` as floats.

OUTPUT:

`"error"` or the minimal cost of the room carpeting, rounded to two decimal places.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
