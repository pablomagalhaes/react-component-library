import React, { useState } from "react";

import NewTable from "./NewTable";

import styled from 'styled-components';

const Styles = styled.div`

  padding: 1rem;

  .frozen {
    background: #f5f5f5;
    -webkit-user-select: none;
    -moz-user-select: none;
    user-select: none;
  }
  .rt-th.frozen {
    border-bottom: 1px solid #f8f8f8;
  }

  .table {
    // display: inline-block;
    // border-spacing: 0;
    // border: 1px solid black;

    .tr {
      background-color: #FFFFFF;
      :last-child {
        .td {
          // border-bottom: 0;
        }
      }
    }

    .th,
    .td {
      margin: 0;
      padding: 0;
      border: 1px solid #353535;
      background-color: #FFFFFF;
      :last-child {
        border-right: 1px solid black;
      }

      input {
        font-size: 1rem;
        padding: 0.5rem;
        margin: 0;
        border: 0;
        width: 100%;
        height: 100%;
      }
    }
  }
`

export interface PureTableProps {
    Data?: Array<string>;
    HeaderWell?: Array<string>;
    HeadersLogs?: Array<string>;
    hideHeader?: boolean;
  }

const PureTable = (props: PureTableProps) => {

    let arr = props.Data;
    let nestedWell = props.HeaderWell;
    console.log('nestedWell', nestedWell);
    let Header = props.HeadersLogs;
    console.log('Header',Header)
    let cols = [];
    let rows = [];
  
    
    let columnsZero: {}[] = [];

    cols.push({
      // @ts-ignore
      Header:  nestedWell[0].label,
      hideHeader: props.hideHeader,
      columns: []
    })
  
    // console.log('cols before', cols);

    // @ts-ignore
    Header.forEach(function(item) {
      let currentCol = {};
       // @ts-ignore
      currentCol['Header'] = item;
      // @ts-ignore
      currentCol['accessor'] = item;
      if(item === 'MD'){
        // @ts-ignore
        currentCol['className'] = 'red';
      }
      columnsZero.push(currentCol);
    });
  
     // @ts-ignore
     cols[0]['columns'] = columnsZero;
     console.log('cols', cols);
     
    // @ts-ignore 
    for (let i = 0; i < arr.length; i++) {
        let row = i;
        let currentRow2 = {};
        cols.map((d, index) => {
          d.columns.map((c, index) => {
            // @ts-ignore
            let valores = Number(arr[row][index]);
            // @ts-ignore
            currentRow2[`${c.accessor}`] = valores;
          })
        })
        rows.push(currentRow2);
        }

    const [data, setData] = useState(rows)
    const [originalData] = useState(data)

      // We need to keep the table from resetting the pageIndex when we
  // Update data. So we can keep track of that flag with a ref.

  // When our cell renderer calls updateMyData, we'll use
  // the rowIndex, columnId and new value to update the
  // original data
  const updateMyData = (rowIndex: number, columnId: any, value: any) => {
    // We also turn on the flag to not reset the page
    setData(old =>
      old.map((row, index) => {
        if (index === rowIndex) {
          return {
            ...old[rowIndex],
            [columnId]: value,
          }
        }
        return row
      })
    )
  }

    // Undo Table
    function undoData(){
        console.log("undo");
        // props.handleCurves();
    };

    // Save Table
    function saveChanges(){
        // console.log("saveChanges nestedHeaders", this.props.nestedHeaders);

        // let nested = this.props.nestedHeaders;
        // console.log("nested", nested);

        // let wellHeaders = nested[0];
        // let logHeaders = nested[1];
        // let wellColumns = [];

        // gets each column well header
        // wellHeaders.forEach((header) => {
        //   for (let i = 0; i < header.colspan; i++) {
        //     wellColumns.push(header.label);
        //   }
        // });

        // formatting json request for saving data in backend
        let payload: any[] = [];

        // for (let i = 0; i < logHeaders.length; i++) {
        //   let column = i;
        //   let well = wellColumns[column];
        //   let log = logHeaders[column];

        //   let wellData = payload.filter((wellData) => wellData.name === well)[0];
        //   let data =
        //     this.hotTableComponent.current.hotInstance.getDataAtCol(column);
        //   if (wellData) {
        //     if (!wellData.logs) {
        //       wellData.logs = [{ name: log, values: data }];
        //     } else {
        //       wellData.logs.push({ name: log, values: data });
        //     }
        //   } else {
        //     wellData = { well_name: well };
        //     wellData.logs = [{ name: log, values: data }];
        //     payload.push(wellData);
        //   }
        // }

        console.log("data antes de salvar", payload);

        // let data = { data: payload };
        // saveEditionData(data)
        //   .then((well_errors) => {
        //     if (well_errors.length === 0) {
        //       setTimeout(
        //         () =>
        //           this.showToastr(
        //             "success",
        //             "Changes were saved succesfully.",
        //             "Success!"
        //           ),
        //         300
        //       );
        //     } else {
        //       let formatted_errors = well_errors.join(", ");
        //       console.log(well_errors);
        //       setTimeout(
        //         () =>
        //           this.showToastr(
        //             "warning",
        //             `An error ocurred in following wells: ${formatted_errors}`,
        //             "Warning"
        //           ),
        //         300
        //       );
        //     }
        //   })
        //   .catch((error) => {
        //     setTimeout(
        //       () =>
        //         this.showToastr("error", "Error while saving changes.", "Error"),
        //       300
        //     );
        //   });
    };

    const resetData = () => setData(originalData);


    return (
        <>
           <Styles>
               <NewTable
                 columns={cols}
                 data={data}
                //  updateMyData={updateMyData}
                 resetData={resetData}
                 exportExcel
                 fileName="table"
                 undoData={undoData}
                 saveChanges={saveChanges}
               />
           </Styles>
        </>
       );
  };
  
  export default PureTable;