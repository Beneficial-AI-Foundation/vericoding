A forest fire has been spotted at *fire*, a simple 2 element array with x, y coordinates.

The forest service has decided to send smoke jumpers in by plane and drop them in the forest.

The terrain is dangerous and surveyors have determined that there are three possible safe *dropzones*, an array of three simple arrays with x, y coordinates. 

The plane is en route and time is of the essence. Your mission is to return a simple [x,y] array with the coordinates of the dropzone closest to the fire. 

EDIT: 
The airplane is leaving from the origin at 0,0. If your result returns two possible dropzones that are both an equal distance from the fire, choose the dropzone that is closest to 0,0.

If the two dropzones are both equal distance away from 0,0, then return the dropzone that is first in the given array. 

For example, if you are given: fire = [1,1], possibleDZ = [0,1],[1,0],[2,2] . The answer is [0,1] because that is the first possible drop zone in the given array.

def dropzone (fire : List Int) (dropzones : List (List Int)) : List Int := sorry

def hypot (x y : Int) : Float := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded