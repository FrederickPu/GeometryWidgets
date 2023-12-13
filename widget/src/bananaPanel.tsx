import { DocumentPosition } from "@leanprover/infoview"
import Banana from "./banana"

export default function HtmlDisplayPanel({pos, geo} : {pos: DocumentPosition, geo : any}):
    JSX.Element {
  return <details open>
    <summary className='mv2 pointer'>GEO Display</summary>
      <Banana pos={pos} geo={geo} />
    </details>
}
