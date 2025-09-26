-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def toString (n : Int) (d : Int) : String :=
sorry

def toDecimal (n : Int) (d : Int) : Float :=
sorry

def intToFloat (i : Int) : Float :=
sorry

def stringToFloat (s : String) : Float :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sign_property (n d : Int) (h : d ≠ 0) :
  let s := toString n d
  (n * d < 0 → s.startsWith "-") ∧
  (n * d > 0 → ¬s.startsWith "-") :=
sorry

theorem format_property (n d : Int) (h : d ≠ 0) :
  let s := toString n d
  let parts := (s.dropWhile (·=='-')).splitOn " "
  match parts with
  | [p] =>
    if p.any (·=='/') then
      let nums := p.splitOn "/"
      nums.length = 2 ∧
      nums[0]!.all Char.isDigit ∧
      nums[1]!.all Char.isDigit
    else
      p.all Char.isDigit
  | [whole, frac] =>
    whole.all Char.isDigit ∧
    let fracParts := frac.splitOn "/"
    fracParts.length = 2 ∧
    fracParts[0]!.all Char.isDigit ∧
    fracParts[1]!.all Char.isDigit ∧
    fracParts[0]!.toNat! < fracParts[1]!.toNat!
  | _ => False :=
sorry

theorem decimal_conversion (n d : Int) (h : d ≠ 0) :
  toDecimal n d = (intToFloat n / intToFloat d) :=
sorry

theorem string_matches_value (n d : Int) (h : d ≠ 0) :
  let s := toString n d
  let val :=
    if s.any (·==' ') then
      let parts := (s.dropWhile (·=='-')).splitOn " "
      let whole := intToFloat parts[0]!.toInt!
      let fracParts := (parts[1]!.splitOn "/")
      let num := intToFloat fracParts[0]!.toInt!
      let den := intToFloat fracParts[1]!.toInt!
      whole + (num / den)
    else if s.any (·=='/') then
      let parts := (s.dropWhile (·=='-')).splitOn "/"
      (intToFloat parts[0]!.toInt!) / (intToFloat parts[1]!.toInt!)
    else
      stringToFloat s
  toDecimal n d = (if s.startsWith "-" then -val else val) :=
sorry
-- </vc-theorems>