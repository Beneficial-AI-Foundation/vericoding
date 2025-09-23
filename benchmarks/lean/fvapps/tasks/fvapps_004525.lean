-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def weather_info (temp : Float) : String := sorry

def celsius_conversion (f : Float) : Float := (f - 32) * (5/9)
-- </vc-definitions>

-- <vc-theorems>
theorem weather_info_returns_string (temp : Float) :
  ∃ s, weather_info temp = s := sorry

theorem weather_info_contains_celsius (temp : Float) :
  ∃ s₁ s₂ : String, weather_info temp = s₁ ++ toString (celsius_conversion temp) ++ s₂ := sorry

theorem weather_info_contains_patterns (temp : Float) :
  ∃ s₁ s₂ s₃ : String, 
    weather_info temp = s₁ ++ "is" ++ s₂ ∧
    weather_info temp = s₃ ++ "temperature" := sorry

theorem weather_info_freezing_threshold (temp : Float) :
  celsius_conversion temp ≤ 0 → 
    ∃ s₁ s₂ : String, weather_info temp = s₁ ++ "freezing temperature" ++ s₂ ∧
  celsius_conversion temp > 0 → 
    ∃ s₁ s₂ : String, weather_info temp = s₁ ++ "above freezing temperature" ++ s₂ := sorry

theorem weather_info_above_freezing {temp : Float} (h : temp > 32) :
  ∃ s₁ s₂ : String, weather_info temp = s₁ ++ "above freezing temperature" ++ s₂ := sorry

theorem weather_info_freezing {temp : Float} (h : temp < 32) :
  ∃ s₁ s₂ : String, weather_info temp = s₁ ++ "freezing temperature" ++ s₂ := sorry
-- </vc-theorems>