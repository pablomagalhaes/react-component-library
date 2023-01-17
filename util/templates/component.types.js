module.exports = (componentName) => ({
    content: `// Gerado em util/create-component.js
  export interface ${componentName}Props {
      foo: string;
  }
  `,
    extension: `.types.ts`
  });