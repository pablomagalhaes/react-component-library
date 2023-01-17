/// <reference types="react" />
export interface PureTableProps {
    Data?: Array<string>;
    HeaderWell?: Array<string>;
    HeadersLogs?: Array<string>;
    hideHeader?: boolean;
}
declare const PureTable: (props: PureTableProps) => JSX.Element;
export default PureTable;
