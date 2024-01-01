import ProofWidgets.Component.HtmlDisplay

open Lean ProofWidgets
open scoped ProofWidgets.Jsx


structure point where
  id : Nat
  x : Float
  y : Float
  deriving ToJson, FromJson
structure edge where
  startNodeId : Nat
  endNodeId : Nat
  deriving ToJson, FromJson
structure BanProps where
  nodes : Array point := #[]
  edges : Array edge := #[]
    deriving ToJson, FromJson, Inhabited

#eval ToJson.toJson ({nodes := #[⟨1, 3.0, 5.0⟩, ⟨2, 4.5, 6.0⟩], edges := #[⟨1, 2⟩]} : BanProps)

@[widget_module]
def Ban : Component BanProps where
  javascript := include_str ".." / ".." / "build" / "js" / "banana.js"

#mkrpcenc BanProps

def eg := #["L", "L", "D⁻¹", "U⁻¹", "L", "D", "D", "L", "U⁻¹", "R", "D", "F", "F", "D"]

#html <Ban nodes={#[(⟨1, 100, 100⟩: point), ⟨2, 20, 20⟩, ⟨3, 50, 40⟩]} edges={#[(⟨1, 2⟩:edge), ⟨3, 1⟩]}/>
