/// <reference types="react" />
import "./style.scss";
export interface NewTableProps {
    columns?: Array<Object>;
    data?: Array<Object>;
    exportExcel?: boolean;
    fileName?: string;
    resetData?: () => void;
    undoData?: () => void;
    saveChanges?: () => void;
}
declare const NewTable: ({ columns, data, exportExcel, fileName, resetData, undoData, saveChanges }: NewTableProps) => JSX.Element;
export default NewTable;
