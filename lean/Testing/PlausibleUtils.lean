import Plausible

namespace Testing.PlausibleUtils

open Plausible

section TacticHelpers

macro "plausible_check" : tactic => `(tactic| plausible (config := { numInst := 100 }))

macro "quick_plausible" : tactic => `(tactic| plausible (config := { numInst := 20 }))

end TacticHelpers

end Testing.PlausibleUtils