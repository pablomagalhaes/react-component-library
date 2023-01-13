import React, { useRef,useState, useEffect, useMemo, useCallback } from "react";

import { Button } from "reactstrap";
import { CornerUpLeft, Download } from "react-feather";
import { useTable, useAbsoluteLayout, useBlockLayout, TableInstance, TableOptions, Column,  } from "react-table";

// import { exportToExcel, getColumns, getRows } from "./excelExport";
import { FixedSizeList } from 'react-window'
import scrollbarWidth from "./scrollbarWidth";

import "./style.scss";

export interface NewTableProps {
    columns?: Array<Object>;
    data?: Array<Object>;
    // updateMyData?: ([]: any[]) => void;
    exportExcel?: boolean;
    fileName?: string;
    resetData?: ()=> void;
    undoData?: ()=> void;
    saveChanges?: ()=> void;
  }

const NewTable = ({ columns, data, exportExcel = false, fileName, resetData, undoData, saveChanges } : NewTableProps ) => {

  // Create an editable cell renderer

  const EditableCell = ({
     // @ts-ignore
    value: initialValue,
     // @ts-ignore
    row: { index },
     // @ts-ignore
    column: { id },
    // updateMyData, // This is a custom function that we supplied to our table instance
  }) => {

    // We need to keep and update the state of the cell normally
    const [value, setValue] = useState(initialValue)

    const onChange = (e: { target: { value: any; }; }) => {
      setValue(e.target.value)
    }

    // We'll only update the external data when the input is blurred
    const onBlur = () => {
    //   updateMyData(index, id, value)
    }

    // If the initialValue is changed external, sync it up with our state
    useEffect(() => {
      setValue(initialValue)
    }, [initialValue])
    if(id === 'MD'){
      return <input value={value}  onChange={onChange} onBlur={onBlur} className='frozen' readOnly />
    }else{
      return <input value={value}  onChange={onChange} onBlur={onBlur} />
    }
    // return <input value={value}  onChange={onChange} onBlur={onBlur} />
  }


  const defaultColumn = {
    Cell: EditableCell,
  }

  const scrollBarSize = useMemo(() => scrollbarWidth(), [])

  const options: TableOptions<{ col1: string; col2: string }> = {
    // @ts-ignore
    data,
    // @ts-ignore
    columns
  };


  // Use the state and functions returned from useTable to build your UI
  const {
    getTableProps,
    getTableBodyProps,
    headerGroups,
    rows,
    totalColumnsWidth,
    prepareRow
  } = useTable({ 
    // @ts-ignore
    columns, 
    // @ts-ignore
    data, 
    defaultColumn
    // updateMyData 
    }, useBlockLayout);


  const tHeadRef = useRef();
  const tBodyRef = useRef();

//   const doExportToExcel = useCallback(() => {
//     const resultColumns = getColumns(columns, defaultColumn);
//     const resultRows = getRows(rows, resultColumns);

//     console.log('resultColumns', resultColumns);
//     console.log('resultRows', resultRows);

//     return exportToExcel(
//       {
//         sheet: {
//           sheetName: fileName || "Excel Export",
//           columns: resultColumns,
//           rows: resultRows,
//         },
//       },
//       `${fileName || "Excel_Export"}_${new Date().toLocaleDateString()}`,
//     );
//   }, [fileName, columns, defaultColumn, rows]);


  const RenderRow = useCallback(
    // @ts-ignore
    ({ index, style }) => {
      const row = rows[index]
      prepareRow(row)
      return (
        <div
          {...row.getRowProps({
            style,
          })}
          className="tr"
        >
          {row.cells.map((cell, ind) => {
            return (
              <div 
              // {...cell.getCellProps()}
              // @ts-ignore
              {...cell.getCellProps({
                // @ts-ignore
                className: `td ${cell.column.className}`
              })}
              // className="td"
              >
                {cell.render('Cell')}
              </div>
            )
          })}
        </div>
      )
    },
    [prepareRow, rows]
  )
  // const RenderRow = useCallback(
  //   ({ index, style }) => {
  //     const row = rows[index]
  //     prepareRow(row)
  //     return (
  //       <tr {...row.getRowProps()}>
  //         {row.cells.map((cell) => {
  //           return <td {...cell.getCellProps()}>{cell.render("Cell")}</td>;
  //         })}
  //       </tr>
  //     )
  //   },
  //   [prepareRow, rows]
  // )


  const react_table = useRef();

    return (
        <>
            <Button
            color="primary"
            onClick={undoData}
            size="md"
            className="shadow-sm mr-1"
            data-tip
            data-for="UndoTip"
            >
            <CornerUpLeft
            className="feather"
            size={30}
            style={{ marginTop: "-5px" }}
            />
            <span style={{ padding: "5px" }}>Undo</span>
            </Button>
            <Button
            color="primary"
            onClick={saveChanges}
            data-tip
            data-for="SaveChangeTip"
            className="shadow-sm mr-1"
            >
            {/* <Filter className="feather" /> */}
            Save Changes
            </Button>
            <Button
            color="primary"
            onClick={resetData}
            data-tip
            data-for="ResetTableTip"
            className="shadow-sm mr-1"
            >
            {/* <RefreshCw className="feather" /> */}
            Reset
            </Button>
            {exportExcel &&
            (
                <> 
                <Button
                    color="primary"
                    // onClick={doExportToExcel}
                    data-tip
                    data-for="ExcelTableTip"
                    className="shadow-sm"
                >
                    <Download
                    className="feather"
                    size={30}
                    style={{ marginTop: "-5px" }}
                    />
                    <span style={{ padding: "5px" }}>Export Excel</span>
                </Button>
                </>  
            )}
            <div
            className="react_table--wrapper"
            style={{ marginTop: "30px"}}
            >
            <table {...getTableProps()}  
            // ref={react_table} 
            id="react_table"
            >
                <thead
                // ref={tHeadRef}
                >
                {headerGroups.map(headerGroup => (
                    <tr {...headerGroup.getHeaderGroupProps()}>
                    {headerGroup.headers.map(column => {
                        return (
                        <th {...column.getHeaderProps()} 
                        className="Colheader"
                        // onClick={(e) => {
                        //     handleClick(e)
                        // }}
                        >
                            {column.render("Header")}
                        </th>
                        );
                    })}
                    </tr>
                ))}
                </thead>
                <tbody 
                // ref={tBodyRef} 
                {...getTableBodyProps()}
                >
                    <FixedSizeList
                    height={400}
                    itemCount={rows.length}
                    itemSize={35}
                    width={totalColumnsWidth+scrollBarSize}
                    >
                    {RenderRow}
                    </FixedSizeList>
                </tbody>
            </table>
            </div>
        </>    
    )
  };
  
export default NewTable;