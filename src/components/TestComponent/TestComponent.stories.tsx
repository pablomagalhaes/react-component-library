import React from "react";
import TestComponent from "./TestComponent";

export default {
  title: "TestComponent"
};

export const WithText = () => (
  <TestComponent
    heading="test component"
    content={<h2>Content</h2>}
  />
);

export const WithButtons = () => (
  <TestComponent
    heading="I have a button"
    content={
      <div>
        <button onClick={() => alert("Hello World!")}>Click me</button>
      </div>
    }
  />
);
