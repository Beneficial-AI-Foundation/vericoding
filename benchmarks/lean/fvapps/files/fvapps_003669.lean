-- <vc-preamble>
def countChar (s : String) (c : Char) : Nat :=
  s.data.filter (· = c) |>.length
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def toOctets (n : Nat) : List Nat := sorry

def int32_to_ip (n : Nat) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem int32_to_ip_has_three_dots (n : Nat)
    (h : n < 2^32) :
    let result := int32_to_ip n
    (countChar result '.' = 3) :=
sorry

theorem int32_to_ip_octets_valid (n : Nat)
    (h : n < 2^32) :
    let octets := toOctets n
    (octets.length = 4 ∧
     octets.all (fun x => x ≤ 255)) :=
sorry

theorem int32_to_ip_preserves_value (n : Nat)
    (h : n < 2^32) :
    let octets := toOctets n
    let reconstructed := (octets.get! 0) * 256^3 +
                        (octets.get! 1) * 256^2 +
                        (octets.get! 2) * 256^1 +
                        (octets.get! 3) * 256^0
    (reconstructed = n) :=
sorry

theorem int32_to_ip_format (octets : List Nat)
    (h1 : octets.length = 4)
    (h2 : octets.all (fun x => x ≤ 255)) :
    let n := (octets.get! 0) * 256^3 +
             (octets.get! 1) * 256^2 +
             (octets.get! 2) * 256^1 +
             (octets.get! 3) * 256^0
    (int32_to_ip n = String.intercalate "." (octets.map toString)) :=
sorry
-- </vc-theorems>