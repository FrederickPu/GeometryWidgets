import React, { useEffect, useRef } from "react";

interface Point {
  x: number;
  y: number;
}

interface Line {
  label: string;
  startPoint: Point;
  endPoint: Point;
}

interface Arc {
  label: string;
  center: Point;
  radius: number;
  startAngle: number;
  endAngle: number;
}

interface ContourProps {
  width: number;
  height: number;
  margin: number;
  nodes: Point[];
  edges: Line[];
  arcs: Arc[];
  selectedLabels?: String;
}

interface BoundingBox {
  minX: number;
  minY: number;
  maxX: number;
  maxY: number;
}

function calculateBoundingBox(lines: Line[], arcs: Arc[]): BoundingBox {
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
  });

  arcs.forEach((arc) => {
    const { center, radius } = arc;
    const arcBoundingBox = {
      minX: center.x - radius,
      minY: center.y - radius,
      maxX: center.x + radius,
      maxY: center.y + radius,
    };

    minX = Math.min(minX, arcBoundingBox.minX);
    minY = Math.min(minY, arcBoundingBox.minY);
    maxX = Math.max(maxX, arcBoundingBox.maxX);
    maxY = Math.max(maxY, arcBoundingBox.maxY);
  });

  return {
    minX,
    minY,
    maxX,
    maxY,
  };
}

export default function Contour(props: ContourProps) {
  const svgElementRef = useRef<SVGSVGElement>(null);

  const { width, height, margin, nodes, edges, arcs, selectedLabels } = props;
  const { minX, minY, maxX, maxY } = calculateBoundingBox(edges, arcs);

  const scaleX = width / (maxX - minX);
  const scaleY = height / (maxY - minY);
  const scale = Math.min(scaleX, scaleY);

  useEffect(() => {
    const svg = svgElementRef.current;

    if (!svg) return;

    // Clear the SVG by removing all child elements
    while (svg.firstChild) {
      svg.removeChild(svg.firstChild);
    }

    svg.setAttribute("width", "100%");
    svg.setAttribute("height", "100%");
    svg.setAttribute("viewBox", `0 0 ${width + 2 * margin} ${height + 2 * margin}`);

    edges.forEach((edge) => {
      const path = document.createElementNS("http://www.w3.org/2000/svg", "path");
      const text = document.createElementNS("http://www.w3.org/2000/svg", "text");

      const { startPoint, endPoint, label } = edge;
      const startX = (startPoint.x - minX) * scale + margin;
      const startY = (startPoint.y - minY) * scale + margin;
      const endX = (endPoint.x - minX) * scale + margin;
      const endY = (endPoint.y - minY) * scale + margin;

      const textCenterX = (startX + endX) / 2;
      const textCenterY = (startY + endY) / 2;

      if (selectedLabels && selectedLabels.includes(label)) {
        path.setAttribute("style", "stroke: red; stroke-width: 3;")
      }
      path.setAttribute("d", `M ${startX} ${startY} L ${endX} ${endY}`);
      path.setAttribute("fill", "none");
      path.setAttribute("stroke", "black");

      text.setAttribute("x", `${textCenterX}`);
      text.setAttribute("y", `${textCenterY}`);
      text.setAttribute("dy", "0.35em");
      text.setAttribute("text-anchor", "middle");
      text.setAttribute("font-size", "5");
      text.textContent = label;

      svg.appendChild(path);
      svg.appendChild(text);
    });

    arcs.forEach((arc) => {
      const path = document.createElementNS("http://www.w3.org/2000/svg", "path");
      const text = document.createElementNS("http://www.w3.org/2000/svg", "text");

      const { center, radius, startAngle, endAngle, label } = arc;
      const arcX = (center.x - minX) * scale + margin;
      const arcY = (center.y - minY) * scale + margin;

      // Convert angles to degrees
      const startAngleDeg = (startAngle * 180) / Math.PI;
      const endAngleDeg = (endAngle * 180) / Math.PI;

      if (selectedLabels && selectedLabels.includes(label)) {
        path.setAttribute("style", "stroke: red; stroke-width: 3;")
      }

      const largeArcFlag = endAngle - startAngle <= Math.PI ? "0" : "1";

      path.setAttribute("d", `M ${arcX + radius * scale * Math.cos(startAngle)} ${arcY + radius * scale * Math.sin(startAngle)} A ${radius * scale} ${radius * scale} 0 ${largeArcFlag} 1 ${arcX + radius * scale * Math.cos(endAngle)} ${arcY + radius * scale * Math.sin(endAngle)}`);
      path.setAttribute("fill", "none");
      path.setAttribute("stroke", "black");

      text.setAttribute("x", `${arc.center.x}`);
      text.setAttribute("y", `${arc.center.y}`);
      text.setAttribute("dy", "0.35em");
      text.setAttribute("text-anchor", "middle");
      text.setAttribute("font-size", "5");
      text.textContent = label;

      svg.appendChild(path);
      svg.appendChild(text);
    });
  }, [width, height, margin, edges, arcs, minX, minY, scale]);

  return <svg ref={svgElementRef}></svg>;
}
