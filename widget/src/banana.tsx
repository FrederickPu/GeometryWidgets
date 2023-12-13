import * as React from 'react';

export default function (props: any) {
  const canvasRef = React.useRef<HTMLCanvasElement | null>(null)
  const {nodes, edges} = props

  React.useEffect(() => {
    const canvas = canvasRef.current;
    if (!canvas){
      return
    }
    const context = canvas.getContext('2d');
    if (!context){
      return
    }
    // Clear the canvas
    context.clearRect(0, 0, canvas.width, canvas.height);
    context.fillStyle = 'white';
    // Draw nodes
    nodes.forEach(node => {
      context.beginPath();
      context.arc(node.x, node.y, 2, 0, 2 * Math.PI);
      context.fillStyle = 'black';
      context.fill();
      context.stroke();
      context.closePath();
    });

    // Draw edges
    edges.forEach(edge => {
      const startNode = nodes.find(node => node.id === edge.startNodeId);
      const endNode = nodes.find(node => node.id === edge.endNodeId);

      context.beginPath();
      context.moveTo(startNode.x, startNode.y);
      context.lineTo(endNode.x, endNode.y);
      context.strokeStyle = 'black';
      context.stroke();
      context.closePath();
    });
  }, [nodes, edges]); // useEffect will run whenever nodes or edges change

  return <canvas ref={canvasRef} width={200} height={200} style={{ border: '1px solid black', backgroundColor: 'white'}} />;
}
