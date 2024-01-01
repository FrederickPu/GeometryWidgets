import ProofWidgets.Component.HtmlDisplay

open Lean ProofWidgets
open scoped ProofWidgets.Jsx

structure point where
  x : Float
  y : Float
  deriving ToJson, FromJson
structure line where
  startPoint : point
  endPoint : point
  deriving ToJson, FromJson
structure arc where
  center : point
  radius : Float
  startAngle : Float
  endAngle : Float
  deriving ToJson, FromJson
structure ContourProps where
  width : Float := 120
  height : Float := 70
  margin : Float := 10
  nodes : Array point := #[]
  edges : Array line := #[]
  arcs : Array arc := #[]
    deriving ToJson, FromJson, Inhabited

@[widget_module]
def Contour : Component ContourProps where
  javascript := include_str ".." / ".." / "build" / "js" / "contour.js"

#html <Contour nodes = {#[⟨20, 20⟩, ⟨4.5, 6.0⟩]} edges = {#[⟨⟨10, 10⟩, ⟨500, 10⟩⟩]} arcs = {#[⟨⟨500, 10⟩, 10, 0, 3.14 * 2⟩, ⟨⟨500 - 20, 10⟩, 20, 0, 3.14⟩]} />
#eval ToJson.toJson ({nodes := #[⟨3.0, 5.0⟩, ⟨4.5, 6.0⟩], edges := #[⟨⟨1.0, 2.0⟩, ⟨50, 50⟩⟩], arcs := #[]} : ContourProps)
