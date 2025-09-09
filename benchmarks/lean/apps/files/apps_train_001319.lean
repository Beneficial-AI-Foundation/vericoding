/-
Sebi lives in Chefland where the government is extremely corrupt that usually makes fool out of public by announcing eye catching but non-sustainable schemes. Recently there was a move to increase tourism in the country that was highly lauded. Sebi wants to examine whether the move has some potential or is a hogwash as usual.
The Chefland is a city with very old road infrastructure. The city has N tourist places. All the places are reachable from each other. The corrupt administrators of the city constructed as few roads as possible just ensuring that all the places are reachable from each other, and those too have now gone old with potholes every here and there. Upon this, there is a toll tax for each road too, which you have to pay once for using that road. Once you pay the tax for a road, you can visit it again as many times as possible.
The tourists coming to Chefland usually want to see all the N nice places. They usually have visit in their own vehicle and stay for few days. Also, they are usually not very rich, they want to pay as less toll tax as possible. For promoting tourism, the government offered their citizens a scheme. It was announced that citizens can choose any two places and the government will build a high class road between those two places and that too without any toll tax. Note that citizens may choose to have a high class road between two cities which already have an old road between them.
Sebi is very sceptical of the claims of the announcement. So, he wants to understand the expected toll tax a tourist has to pay to tour the entire city considering that the citizens of Chefland vote for the two cities for constructing high road uniformly randomly. Can you please him in finding this?

-----Input-----
There is a single test case per test file.
The first line of the input contains an integer N denoting the number of tourist spots in Chefland.
Each of the he next N - 1 lines contains three space separated integers u, v, c, denoting that there is a road between tourist spot u and v which has a toll tax of c Rs.

-----Output-----
Output a single line containing the expected toll tax a tourist has to pay for visiting all the N spots after the construction of new road. Your answer will be considered correct if it has an absolute error less than or equal to 1e-2.

-----Constraints-----
- 2 ≤ N ≤ 105
- 1 ≤ u, v ≤ N
- 0 ≤ c ≤ 106

-----Example-----
Input:
3
1 2 3
1 3 2

Output:
2.333333

-----Explanation-----
Assume that the citizens construct the high class road between city 1 and 2. A tourist can visit all the places by just paying a toll tax of 2 Rs.
If the high class road is constructed between city 1 and 3. All the places then can be visited by just paying a toll tax of 3 Rs.
If the cities 2 and 3 are connected by the high class road. All the places can be visited by paying a toll tax of 2Rs. 
Hence expected Rs. that a tourist has to pay in toll tax will be (2 + 3 + 2) / 3 = 7 / 3 = 2.333333
-/

def solve_tourist_spots (n : Nat) (roads : List String) : Float :=
sorry

-- <vc-helpers>
-- </vc-helpers>

def isValidRoad : String → Bool :=
sorry

theorem solve_tourist_spots_output_is_float (n : Nat) (roads : List String) 
    (h : n ≥ 2) (h2 : roads.length > 0) :
  ∃ (f : Float), solve_tourist_spots n roads = f :=
sorry

theorem solve_tourist_spots_total_weight 
    {n : Nat} {roads : List String} {weights : List Float}
    (h : n ≥ 2)
    (h2 : roads.length > 0) 
    (h3 : weights = roads.map (fun r => sorry)) :
  solve_tourist_spots n roads ≤ weights.foldl (. + .) 0.0 :=
sorry

theorem solve_tourist_spots_invalid_input
    {n : Nat} {roads : List String}
    (h : n ≥ 2)
    (h2 : ∃ r ∈ roads, ¬ isValidRoad r) :
  solve_tourist_spots n roads = 0.0 :=
sorry

-- Apps difficulty: interview
-- Assurance level: guarded