import * as React from "react";

export default function (props) {
  return React.createElement(
    "div",
    {
      style: {
        display: "grid",
        gridTemplateColumns: "repeat(12, 20px)",
        gridTemplateRows: "repeat(9, 20px)",
        rowGap: "2px",
        columnGap: "2px",
        margin: "10px",
      },
    },
    React.createElement("div", {
      style: { gridColumn: "4", gridRow: "1", backgroundColor: red },
    }),
    React.createElement("div", {
      style: {
        gridColumn: "5",
        gridRow: "1",
        backgroundColor: "#ff0000",
      },
    })
  );
}
