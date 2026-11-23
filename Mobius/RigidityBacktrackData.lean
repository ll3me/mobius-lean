import Mobius.RigidityKernelData
namespace Mobius.Rigidity.Backtracks
open Mobius.SignObstruction (B)
open Mobius.Rigidity.Kernel (double key)
set_option maxRecDepth 16384
set_option maxHeartbeats 20000000

def mask (x y : B) := double.coefficient (key false x y) ^^^ double.coefficient (key true x y)
def linMask (x : B) := mask x x ^^^ mask 0 0

theorem mask_form : ∀ x y : B, mask x y = mask 0 (x ^^^ y) ^^^ linMask x := by decide +kernel
theorem mask_linear : ∀ x y : B, linMask (x ^^^ y) = linMask x ^^^ linMask y := by decide +kernel

end Mobius.Rigidity.Backtracks
