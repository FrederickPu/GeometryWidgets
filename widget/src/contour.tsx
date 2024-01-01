// TypeScript equivalent for the Lean structures

import React, { useEffect, useRef } from "react";
import * as d3 from "d3";


interface point {
  x: number;
  y: number;
}

interface line {
  startPoint: point;
  endPoint: point;
}

interface arc {
  center: point;
  radius: number;
  startAngle: number;
  endAngle: number;
}

interface ContourProps {
  width: number;
  height: number;
  margin: number;
  nodes: point[];
  edges: line[];
  arcs: arc[];
}

interface boundingBox {
  minX: number;
  minY: number;
  maxX: number;
  maxY: number;
}

function calculateBoundingBox(lines : line[], arcs : arc[]): boundingBox {
  let minX = Infinity;
  let minY = Infinity;
  let maxX = -Infinity;
  let maxY = -Infinity;

  lines.forEach((line) => {
      const { startPoint, endPoint } = line;
      minX = Math.min(minX, startPoint.x, endPoint.x);
      minY = Math.min(minY, startPoint.y, endPoint.y);
      maxX = Math.max(maxX, startPoint.x, endPoint.x);
      maxY = Math.max(maxY, startPoint.y, endPoint.y);
  })
  arcs.forEach((arc) => {
    const { center, radius, startAngle, endAngle } = arc;

      minX = Math.min(minX, center.x - radius);
      minY = Math.min(minY, center.y - radius);
      maxX = Math.max(maxX, center.x + radius);
      maxY = Math.max(maxY, center.y + radius);
  })


  return {
    minX,
    minY,
    maxX,
    maxY,
  };
}

export default function Contour(props: ContourProps) {
  const svgRef = useRef(null);

  const {width, height, margin, nodes, edges, arcs} = props
  const { minX, minY, maxX, maxY } = calculateBoundingBox(edges, arcs)

  const scaleX = width / (maxX - minX)
  const scaleY = height / (maxY - minY)
  const scale = Math.min(scaleX, scaleY)

  useEffect(() => {

    const svg = d3
    .select(svgRef.current)
    .attr("width", "100%")
    .attr("height", "100%")
    .attr("viewBox", `0 0 ${width + 2 * margin} ${height + 2 * margin}`)
    .style("background-color", "white");

    svg.selectAll("path").remove();

    nodes.forEach(node => {
      // do nothing for now
    })
    edges.forEach(edge => {
      var path = d3.path()
      path.moveTo((edge.startPoint.x - minX) * scale + margin, (edge.startPoint.y - minY) * scale + margin)
      path.lineTo((edge.endPoint.x - minX) * scale + margin, (edge.endPoint.y - minY) * scale + margin)

      svg
      .append("path")
      .attr("d", path.toString())
      .attr("fill", "none")
      .attr("stroke", "black");
    })
    arcs.forEach(arc => {
      var path = d3.path()
      path.arc((arc.center.x - minX) * scale + margin, (arc.center.y - minY) * scale + margin, arc.radius * scale, arc.startAngle, arc.endAngle)

      svg
      .append("path")
      .attr("d", path.toString())
      .attr("fill", "none")
      .attr("stroke", "black");
    })
  })
  return <svg ref={svgRef}></svg>;
}
