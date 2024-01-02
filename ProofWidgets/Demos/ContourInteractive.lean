import ProofWidgets.Component.HtmlDisplay

open Lean ProofWidgets
open scoped ProofWidgets.Jsx

structure point where
  x : Float
  y : Float
  deriving ToJson, FromJson
structure line where
  label : String
  startPoint : point
  endPoint : point
  deriving ToJson, FromJson
structure arc where
  labe : String
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
  selectedLabels : Option (Array String) := none
    deriving ToJson, FromJson, Inhabited

@[widget_module]
def Contour : Component ContourProps where
  javascript := include_str ".." / ".." / "build" / "js" / "contour.js"

#html <Contour nodes = {#[⟨20, 20⟩, ⟨4.5, 6.0⟩]} edges = {#[⟨"klj", ⟨10, 10⟩, ⟨500, 10⟩⟩, ⟨"kl", ⟨10, 10⟩, ⟨10, 500⟩⟩]} arcs = {#[⟨"l", ⟨500, 10⟩, 10, 0, 3.14 * 2⟩, ⟨"h7", ⟨500 - 20, 10⟩, 40, 0, 3.14⟩]} selectedLabels={#["klj"]}/>
#eval ToJson.toJson ({nodes := #[⟨20, 20⟩, ⟨4.5, 6.0⟩], edges := #[⟨"", ⟨10, 10⟩, ⟨500, 10⟩⟩], arcs := #[⟨"lkj", ⟨500, 10⟩, 10, 0, 3.14 * 2⟩, ⟨"h7", ⟨500 - 20, 10⟩, 20, 0, 3.14⟩]} : ContourProps)
-- #eval ToJson.toJson ({nodes := #[⟨3.0, 5.0⟩, ⟨4.5, 6.0⟩], edges := #[⟨⟨1.0, 2.0⟩, ⟨50, 50⟩⟩], arcs := #[]} : ContourProps)
