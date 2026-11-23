import Mobius.RigidityKernelData

/-! Every generator of the 62-dimensional zero-syndrome space has a
separable diagonal derivative in each direction. One bit per generator
is packed into each natural number. -/
namespace Mobius.Rigidity.Residual
open Mobius.SignObstruction (B)
open Mobius.Rigidity.Kernel (double key)
set_option maxRecDepth 16384
set_option maxHeartbeats 50000000

def mask (d x y : B) := double.coefficient (key false x y) ^^^
  double.coefficient (key false (x ^^^ d) (y ^^^ d))

theorem checked_mask : ∀ (d x y : B), mask d x y =
    mask d x 0 ^^^ mask d 0 y ^^^ mask d 0 0 := by decide +kernel

end Mobius.Rigidity.Residual
