predicate isValidInput(input: string)
{
    |input| > 0 &&
    true // Simplified for placeholder
}

predicate isValidOutput(output: string)
{
    |output| > 0 &&
    (output == "-1\n" || 
     (output != "-1\n" && |output| > 1 && output[|output|-1] == '\n'))
}

datatype GridData = GridData(h: int, w: int, cells: seq<seq<char>>)

predicate validGrid(grid: GridData)
{
    grid.h > 0 && grid.w > 0 && 
    |grid.cells| == grid.h &&
    (forall i :: 0 <= i < grid.h ==> |grid.cells[i]| == grid.w) &&
    (forall i, j :: 0 <= i < grid.h && 0 <= j < grid.w ==> 
        grid.cells[i][j] == '.' || grid.cells[i][j] == '#') &&
    grid.cells[0][0] == '.' && grid.cells[grid.h-1][grid.w-1] == '.'
}

function parseInput(input: string): GridData
    requires isValidInput(input)
    ensures validGrid(parseInput(input))
{
    GridData(1, 1, [['.']])
}

predicate pathExists(grid: GridData)
    requires validGrid(grid)
{
    true
}

function maxChangeableWhiteCells(grid: GridData): int
    requires validGrid(grid)
    requires pathExists(grid)
    ensures 0 <= maxChangeableWhiteCells(grid) <= countWhiteCells(grid) - 2
    ensures maxChangeableWhiteCells(grid) == countWhiteCells(grid) - minCutSize(grid)
{
    0
}

function countWhiteCells(grid: GridData): int
    requires validGrid(grid)
    ensures countWhiteCells(grid) >= 2
{
    2
}

function minCutSize(grid: GridData): int
    requires validGrid(grid)
    requires pathExists(grid)
    ensures minCutSize(grid) >= 2
    ensures minCutSize(grid) <= countWhiteCells(grid)
{
    2
}

// <vc-helpers>
function intToString(n: int): string
  requires n >= 0
  ensures (n == 0) ==> (intToString(n) == "0")
  ensures (n > 0) ==> (|intToString(n)| > 0)
  ensures forall k :: 0 <= k < |intToString(n)| ==> '0' <= intToString(n)[k] <= '9'
{
  if n == 0 then "0"
  else
    var s := "";
    var temp := n;
    while temp > 0
      invariant temp >= 0
      invariant (temp == 0) ==> (s != "" || n == 0)
      invariant (temp > 0) ==> (n > 0)
      invariant temp < n ==> |s| > 0
      invariant forall k :: 0 <= k < |s| ==> '0' <= s[k] <= '9'
      invariant n == temp * (10 * (10*( * )) ) +  // This invariant is not easily expressed with just temp and s
                (var current_s_val := 0; 
                 if |s| > 0 then (
                   for k := 0 to |s|-1 {
                     current_s_val := current_s_val * 10 + (s[k] as int - '0' as int);
                   }
                 ) else ( current_s_val := 0);
                 n) == temp * (Pow10(|s|)) + current_s_val
    {
      s := (temp % 10).ToString() + s;
      temp := temp / 10;
    }
    s
}

function Pow10(exp: int): int
  requires exp >= 0
  ensures Pow10(exp) > 0
  ensures Pow10(0) == 1
  ensures exp > 0 ==> Pow10(exp) == 10 * Pow10(exp - 1)
{
  if exp == 0 then 1
  else 10 * Pow10(exp - 1)
}

function valueOfString(s: string): int
  requires forall k :: 0 <= k < |s| ==> '0' <= s[k] <= '9'
  requires |s| > 0
{
  var val := 0;
  for k := 0 to |s|-1 {
    val := val * 10 + (s[k] as int - '0' as int);
  }
  val
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (output: string)
    requires |stdin_input| > 0
    requires isValidInput(stdin_input)
    ensures isValidOutput(output)
    ensures output == "-1\n" || 
            (exists result: int :: result >= 0 && output == intToString(result) + "\n")
    ensures output == "-1\n" <==> !pathExists(parseInput(stdin_input))
    ensures output != "-1\n" ==> 
            (exists result: int, grid: GridData :: 
                grid == parseInput(stdin_input) &&
                result == maxChangeableWhiteCells(grid) &&
                output == intToString(result) + "\n")
// </vc-spec>
// <vc-code>
{
  var grid := parseInput(stdin_input);

  if !pathExists(grid) then
    output := "-1\n";
  else
    var result := maxChangeableWhiteCells(grid);
    output := intToString(result) + "\n";
  return output;
}
// </vc-code>

