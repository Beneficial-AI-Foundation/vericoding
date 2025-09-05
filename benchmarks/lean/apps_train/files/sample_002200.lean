You are in charge of controlling a dam. The dam can store at most L liters of water. Initially, the dam is empty. Some amount of water flows into the dam every morning, and any amount of water may be discharged every night, but this amount needs to be set so that no water overflows the dam the next morning.
It is known that v_i liters of water at t_i degrees Celsius will flow into the dam on the morning of the i-th day.
You are wondering about the maximum possible temperature of water in the dam at noon of each day, under the condition that there needs to be exactly L liters of water in the dam at that time. For each i, find the maximum possible temperature of water in the dam at noon of the i-th day. Here, consider each maximization separately, that is, the amount of water discharged for the maximization of the temperature on the i-th day, may be different from the amount of water discharged for the maximization of the temperature on the j-th day (j≠i).
Also, assume that the temperature of water is not affected by anything but new water that flows into the dam. That is, when V_1 liters of water at T_1 degrees Celsius and V_2 liters of water at T_2 degrees Celsius are mixed together, they will become V_1+V_2 liters of water at \frac{T_1*V_1+T_2*V_2}{V_1+V_2} degrees Celsius, and the volume and temperature of water are not affected by any other factors.

-----Constraints-----
 - 1≤ N ≤ 5*10^5
 - 1≤ L ≤ 10^9
 - 0≤ t_i ≤ 10^9(1≤i≤N)
 - 1≤ v_i ≤ L(1≤i≤N)
 - v_1 = L
 - L, each t_i and v_i are integers.

-----Input-----
Input is given from Standard Input in the following format:
N L
t_1 v_1
t_2 v_2
:
t_N v_N

-----Output-----
Print N lines. The i-th line should contain the maximum temperature such that it is possible to store L liters of water at that temperature in the dam at noon of the i-th day.
Each of these values is accepted if the absolute or relative error is at most 10^{-6}.

-----Sample Input-----
3 10
10 10
20 5
4 3

-----Sample Output-----
10.0000000
15.0000000
13.2000000

 - On the first day, the temperature of water in the dam is always 10 degrees: the temperature of the only water that flows into the dam on the first day.
 - 10 liters of water at 15 degrees of Celsius can be stored on the second day, by discharging 5 liters of water on the night of the first day, and mix the remaining water with the water that flows into the dam on the second day.
 - 10 liters of water at 13.2 degrees of Celsius can be stored on the third day, by discharging 8 liters of water on the night of the first day, and mix the remaining water with the water that flows into the dam on the second and third days.

def Water.subtract (w : Water) (v : Float) : Water :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: unguarded