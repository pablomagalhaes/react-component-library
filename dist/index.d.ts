/// <reference types="react" />
interface PureTableProps {
    Data?: Array<string>;
    HeaderWell?: Array<string>;
    HeadersLogs?: Array<string>;
}
declare const PureTable: (props: PureTableProps) => JSX.Element;

interface ButtonProps {
    label: string;
}
declare const Button: (props: ButtonProps) => JSX.Element;

export { Button, PureTable };
